package lisa.kernel.fol

import scala.annotation.tailrec
import scala.collection.mutable
import scala.math.Numeric.IntIsIntegral

/**
 * An EquivalenceChecker is an object that allows to detect some notion of equivalence between formulas
 * and between terms.
 * This allows the proof checker and writer to avoid having to deal with a class of "easy" equivalence.
 * For example, by considering "x ∨ y" as being the same formula as "y ∨ x", we can avoid frustrating errors.
 * For soundness, this relation should always be a subrelation of the usual FOL implication.
 * The implementation checks for Orthocomplemented Bismeilatices equivalence, plus symetry and reflexivity
 * of equality and alpha-equivalence.
 */
private[fol] trait EquivalenceChecker extends FormulaDefinitions {
  sealed abstract class SimpleFormula {
    val size: Int
    private[EquivalenceChecker] var normalForm: Option[NormalFormula] = None
  }
  case class SimplePredicate(id: PredicateLabel, args: List[Term]) extends SimpleFormula {
    val size = 1
  }
  case class SimpleConnector(id: ConnectorLabel, args: List[SimpleFormula]) extends SimpleFormula {
    val size = 1
  }
  case class SNeg(child: SimpleFormula) extends SimpleFormula {
    val size: Int = 1 + child.size
  }
  case class SOr(children: List[SimpleFormula]) extends SimpleFormula {
    val size: Int = (children map (_.size)).foldLeft(1) { case (a, b) => a + b }
  }
  case class SForall(x: String, inner: SimpleFormula) extends SimpleFormula {
    val size: Int = 1 + inner.size
  }
  case class SExists(x: String, inner: SimpleFormula) extends SimpleFormula {
    val size: Int = 1 + inner.size
  }
  case class SLiteral(b: Boolean) extends SimpleFormula {
    val size = 1
    normalForm = Some(NLiteral(b))
  }
  sealed abstract class NormalFormula {
    val code: Int
  }
  case class NormalPredicate(id: PredicateLabel, args: List[Term], code: Int) extends NormalFormula
  case class NormalConnector(id: ConnectorLabel, args: List[NormalFormula], code: Int) extends NormalFormula
  case class NNeg(child: NormalFormula, code: Int) extends NormalFormula
  case class NOr(children: List[NormalFormula], code: Int) extends NormalFormula
  case class NForall(x: String, inner: NormalFormula, code: Int) extends NormalFormula
  case class NExists(x: String, inner: NormalFormula, code: Int) extends NormalFormula
  case class NLiteral(b: Boolean) extends NormalFormula {
    val code: Int = if (b) 1 else 0
  }

  /**
   * A class that encapsulate "runtime" information of the equivalence checker. It performs memoization for efficiency.
   */
  class LocalEquivalenceChecker {
    private val unsugaredVersion = scala.collection.mutable.HashMap[Formula, SimpleFormula]()

    // transform a LISA formula into a simpler, desugarised version with less symbols. Conjunction, implication, iff, existsOne are treated as alliases and translated.
    def removeSugar(phi: Formula): SimpleFormula = unsugaredVersion.getOrElseUpdate(
      phi, {
        phi match {
          case PredicateFormula(label, args) => SimplePredicate(label, args.toList)
          case ConnectorFormula(label, args) =>
            label match {
              case Neg => SNeg(removeSugar(args(0)))
              case Implies =>
                val l = removeSugar(args(0))
                val r = removeSugar(args(1))
                SOr(List(SNeg(l), r))
              case Iff =>
                val l = removeSugar(args(0))
                val r = removeSugar(args(1))
                val c1 = SNeg(SOr(List(SNeg(l), r)))
                val c2 = SNeg(SOr(List(SNeg(r), l)))
                SNeg(SOr(List(c1, c2)))
              case And =>
                SNeg(SOr(args.map(c => SNeg(removeSugar(c))).toList))
              case Or => SOr((args map removeSugar).toList)
              case _ => SimpleConnector(label, args.toList.map(removeSugar))
            }
          case BinderFormula(label, bound, inner) =>
            label match {
              case Forall => SForall(bound.id, removeSugar(inner))
              case Exists => SExists(bound.id, removeSugar(inner))
              case ExistsOne =>
                val y = VariableLabel(freshId(inner.freeVariables.map(_.id), bound.id))
                val c1 = SimplePredicate(equality, List(VariableTerm(bound), VariableTerm(y)))
                val c2 = removeSugar(inner)
                val c1_c2 = SOr(List(SNeg(c1), c2))
                val c2_c1 = SOr(List(SNeg(c2), c1))
                SExists(y.id, SForall(bound.id, SNeg(SOr(List(SNeg(c1_c2), SNeg(c2_c1))))))
            }
        }
      }
    )

    def toLocallyNameless(t: Term, subst: Map[VariableLabel, Int], i: Int): Term = t match {
      case Term(label:VariableLabel, _) =>
        if (subst.contains(label)) VariableTerm(VariableLabel("x" + (i - subst(label))))
        else VariableTerm(VariableLabel("_" + label))
      case Term(label, args) => Term(label, args.map(c => toLocallyNameless(c, subst, i)))
    }

    def toLocallyNameless(phi: SimpleFormula, subst: Map[VariableLabel, Int], i: Int): SimpleFormula = phi match {
      case SimplePredicate(id, args) => SimplePredicate(id, args.map(c => toLocallyNameless(c, subst, i)))
      case SimpleConnector(id, args) => SimpleConnector(id, args.map(f => toLocallyNameless(f, subst, i)))
      case SNeg(child) => SNeg(toLocallyNameless(child, subst, i))
      case SOr(children) => SOr(children.map(toLocallyNameless(_, subst, i)))
      case SForall(x, inner) => SForall("", toLocallyNameless(inner, subst + (VariableLabel(x) -> i), i + 1))
      case SExists(x, inner) => SExists("", toLocallyNameless(inner, subst + (VariableLabel(x) -> i), i + 1))
      case SLiteral(b) => phi
    }

    private val codesSig: mutable.HashMap[(String, Seq[Int]), Int] = mutable.HashMap()
    codesSig.update(("zero", Nil), 0)
    codesSig.update(("one", Nil), 1)

    val codesTerms: mutable.HashMap[Term, Int] = mutable.HashMap()
    val codesSigTerms: mutable.HashMap[(TermLabel, Seq[Int]), Int] = mutable.HashMap()

    def codesOfTerm(t: Term): Int = codesTerms.getOrElseUpdate(
      t,
      t match {
        case Term(label:VariableLabel, _) =>
          codesSigTerms.getOrElseUpdate((label, Nil), codesSigTerms.size)
        case Term(label, args) =>
          val c = args map codesOfTerm

          codesSigTerms.getOrElseUpdate((label, c), codesSigTerms.size)
      }
    )

    /*
        def hasNormaleRecComputed(sf:SimpleFormula): Boolean = sf.normalForm.nonEmpty && (sf match {
            case SNeg(child) => hasNormaleRecComputed(child)
            case SOr(children) => children.forall(c => hasNormaleRecComputed(c))
            case SForall(x, inner) => hasNormaleRecComputed(inner)
            case SExists(x, inner) => hasNormaleRecComputed(inner)
            case _ => true
        })
     */
    def checkForContradiction(children: List[(NormalFormula, Int)]): Boolean = {
      val (negatives_temp, positives_temp) = children.foldLeft[(List[NormalFormula], List[NormalFormula])]((Nil, Nil))((acc, ch) =>
        acc match {
          case (negatives, positives) =>
            ch._1 match {
              case NNeg(child, c) => (child :: negatives, positives)
              case _ => (negatives, ch._1 :: positives)
            }
        }
      )
      val (negatives, positives) = (negatives_temp.sortBy(_.code), positives_temp.reverse)
      var i, j = 0
      while (i < positives.size && j < negatives.size) { // checks if there is a positive and negative nodes with same code.
        val (c1, c2) = (positives(i).code, negatives(j).code)
        if (c1 < c2) i += 1
        else if (c1 == c2) return true
        else j += 1
      }
      var k = 0
      val children_codes = children.map(c => c._2).toSet // check if there is a negated disjunction whose children all share a code with an uncle
      while (k < negatives.size) {
        negatives(k) match {
          case NOr(gdChildren, c) =>
            if (gdChildren.forall(sf => children_codes.contains(sf.code))) return true
          case _ => ()
        }
        k += 1
      }
      false
    }

    def updateCodesSig(sig: (String, Seq[Int])): Int = {
      if (!codesSig.contains(sig)) codesSig.update(sig, codesSig.size)
      codesSig(sig)
    }

    def OCBSLCode(phi: SimpleFormula): Int = {
      if (phi.normalForm.nonEmpty) return phi.normalForm.get.code
      val L = pDisj(phi, Nil)
      val L2 = L zip (L map (_.code))
      val L3 = L2.sortBy(_._2).distinctBy(_._2).filterNot(_._2 == 0) // actually efficient has set based implementation already
      if (L3.isEmpty) {
        phi.normalForm = Some(NLiteral(false))
      } else if (L3.length == 1) {
        phi.normalForm = Some(L3.head._1)
      } else if (L3.exists(_._2 == 1) || checkForContradiction(L3)) {
        phi.normalForm = Some(NLiteral(true))
      } else {
        phi.normalForm = Some(NOr(L3.map(_._1), updateCodesSig(("or", L3.map(_._2)))))
      }
      phi.normalForm.get.code
    }

    def pDisj(phi: SimpleFormula, acc: List[NormalFormula]): List[NormalFormula] = {
      if (phi.normalForm.nonEmpty) return pDisjNormal(phi.normalForm.get, acc)
      val r: List[NormalFormula] = phi match {
        case SimplePredicate(id, args) =>
          val lab = "pred_" + id.id + "_" + id.arity
          if (id == equality) {
            if (codesOfTerm(args(0)) == codesOfTerm(args(1)))
              phi.normalForm = Some(NLiteral(true))
            else
              phi.normalForm = Some(NormalPredicate(id, args, updateCodesSig((lab, (args map codesOfTerm).sorted))))
          } else {
            phi.normalForm = Some(NormalPredicate(id, args, updateCodesSig((lab, args map codesOfTerm))))
          }
          phi.normalForm.get :: acc
        case SimpleConnector(id, args) =>
          val lab = "conn_" + id.id + "_" + id.arity
          phi.normalForm = Some(NormalConnector(id, args.map(_.normalForm.get), updateCodesSig((lab, args map OCBSLCode))))
          phi.normalForm.get :: acc
        case SNeg(child) => pNeg(child, phi, acc)
        case SOr(children) => children.foldLeft(acc)((p, a) => pDisj(a, p))
        case SForall(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NForall(x, inner.normalForm.get, updateCodesSig(("forall", List(r)))))
          phi.normalForm.get :: acc
        case SExists(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NExists(x, inner.normalForm.get, updateCodesSig(("exists", List(r)))))
          phi.normalForm.get :: acc
        case SLiteral(true) =>
          phi.normalForm = Some(NLiteral(true))
          phi.normalForm.get :: acc
        case SLiteral(false) =>
          phi.normalForm = Some(NLiteral(false))
          phi.normalForm.get :: acc
      }
      r
    }

    def pNeg(phi: SimpleFormula, parent: SimpleFormula, acc: List[NormalFormula]): List[NormalFormula] = {
      if (phi.normalForm.nonEmpty) return pNegNormal(phi.normalForm.get, parent, acc)
      val r: List[NormalFormula] = phi match {
        case SimplePredicate(id, args) =>
          val lab = "pred_" + id.id + "_" + id.arity
          if (id == equality) {
            if (codesOfTerm(args(0)) == codesOfTerm(args(1))) {
              phi.normalForm = Some(NLiteral(true))
              parent.normalForm = Some(NLiteral(false))
            } else {
              phi.normalForm = Some(NormalPredicate(id, args, updateCodesSig((lab, (args map codesOfTerm).sorted))))
              parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
            }
          } else {
            phi.normalForm = Some(NormalPredicate(id, args, updateCodesSig((lab, args map codesOfTerm))))
            parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
          //phi.normalForm = Some(NormalPredicate(id, args, updateCodesSig((lab, args map codesOfTerm))))
          }
          parent.normalForm.get :: acc
        case SimpleConnector(id, args) =>
          val lab = "conn_" + id.id + "_" + id.arity
          phi.normalForm = Some(NormalConnector(id, args.map(_.normalForm.get), updateCodesSig((lab, args map OCBSLCode))))
          parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
          parent.normalForm.get :: acc
        case SNeg(child) => pDisj(child, acc)
        case SForall(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NForall(x, inner.normalForm.get, updateCodesSig(("forall", List(r)))))
          parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
          parent.normalForm.get :: acc
        case SExists(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NExists(x, inner.normalForm.get, updateCodesSig(("exists", List(r)))))
          parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
          parent.normalForm.get :: acc
        case SLiteral(true) =>
          parent.normalForm = Some(NLiteral(false))
          parent.normalForm.get :: acc
        case SLiteral(false) =>
          parent.normalForm = Some(NLiteral(true))
          parent.normalForm.get :: acc
        case SOr(children) =>
          if (children.isEmpty) {
            parent.normalForm = Some(NLiteral(true))
            parent.normalForm.get :: acc
          } else {
            val T = children.sortBy(_.size)
            val r1 = T.tail.foldLeft(List[NormalFormula]())((p, a) => pDisj(a, p))
            val r2 = r1 zip (r1 map (_.code))
            val r3 = r2.sortBy(_._2).distinctBy(_._2).filterNot(_._2 == 0)
            if (r3.isEmpty) pNeg(T.head, parent, acc)
            else {
              val s1 = pDisj(T.head, r1)
              val s2 = s1 zip (s1 map (_.code))
              val s3 = s2.sortBy(_._2).distinctBy(_._2).filterNot(_._2 == 0)
              if (s3.exists(_._2 == 1) || checkForContradiction(s3)) {
                phi.normalForm = Some(NLiteral(true))
                parent.normalForm = Some(NLiteral(false))
                parent.normalForm.get :: acc
              } else if (s3.length == 1) {
                pNegNormal(s3.head._1, parent, acc)
              } else {
                phi.normalForm = Some(NOr(s3.map(_._1), updateCodesSig(("or", s3.map(_._2)))))
                parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
                parent.normalForm.get :: acc
              }
            }
          }
      }
      r
    }
    def pDisjNormal(f: NormalFormula, acc: List[NormalFormula]): List[NormalFormula] = f match {
      case NOr(children, c) => children ++ acc
      case p @ _ => p :: acc
    }
    def pNegNormal(f: NormalFormula, parent: SimpleFormula, acc: List[NormalFormula]): List[NormalFormula] = f match {
      case NNeg(child, c) =>
        pDisjNormal(child, acc)
      case _ =>
        parent.normalForm = Some(NNeg(f, updateCodesSig(("neg", List(f.code)))))
        parent.normalForm.get :: acc
    }

    def check(formula1: Formula, formula2: Formula): Boolean = {
      getCode(formula1) == getCode(formula2)
    }
    def getCode(formula: Formula): Int = OCBSLCode(toLocallyNameless(removeSugar(formula), Map.empty, 0))

    def isSame(term1: Term, term2: Term): Boolean = codesOfTerm(term1) == codesOfTerm(term2)

    def isSame(formula1: Formula, formula2: Formula): Boolean = {
      this.check(formula1, formula2)
    }

    def isSameSet(s1: Set[Formula], s2: Set[Formula]): Boolean = {
      s1.map(this.getCode).toList.sorted == s2.map(this.getCode).toList.sorted
    }

    def isSubset(s1: Set[Formula], s2: Set[Formula]): Boolean = {
      val codesSet1 = s1.map(this.getCode)
      val codesSet2 = s2.map(this.getCode)
      codesSet1.subsetOf(codesSet2)

    }
    def contains(s: Set[Formula], f: Formula): Boolean = {
      val codesSet = s.map(this.getCode)
      val codesFormula = this.getCode(f)
      codesSet.contains(codesFormula)
    }

  }
  def isSame(term1: Term, term2: Term): Boolean = (new LocalEquivalenceChecker).isSame(term1, term2)

  def isSame(formula1: Formula, formula2: Formula): Boolean = (new LocalEquivalenceChecker).isSame(formula1, formula2)

  def isSameSet(s1: Set[Formula], s2: Set[Formula]): Boolean = (new LocalEquivalenceChecker).isSameSet(s1, s2)

  def isSubset(s1: Set[Formula], s2: Set[Formula]): Boolean = (new LocalEquivalenceChecker).isSubset(s1, s2)

  def contains(s: Set[Formula], f: Formula): Boolean = (new LocalEquivalenceChecker).contains(s, f)
}
