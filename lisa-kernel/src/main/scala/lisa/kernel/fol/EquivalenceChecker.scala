package lisa.kernel.fol

import java.lang
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
 * See https://github.com/epfl-lara/OCBSL for more informations
 */
private[fol] trait EquivalenceChecker extends FormulaDefinitions {

  def reducedForm(formula: Formula): Formula = {
    val p = simplify(formula)
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toFormulaAIG(fln)
    res
  }

  def reducedNNFForm(formula: Formula): Formula = {
    val p = simplify(formula)
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toFormulaNNF(fln)
    res
  }
  def reduceSet(s: Set[Formula]): Set[Formula] = {
    var res: List[Formula] = Nil
    s.map(reducedForm)
      .foreach({ f =>
        if (!res.exists(isSame(f, _))) res = f :: res
      })
    res.toSet
  }

  def isSameTerm(term1: Term, term2: Term): Boolean = term1.label == term2.label && term1.args.lazyZip(term2.args).forall(isSameTerm)
  def isSame(formula1: Formula, formula2: Formula): Boolean = {
    val nf1 = computeNormalForm(simplify(formula1))
    val nf2 = computeNormalForm(simplify(formula2))
    latticesEQ(nf1, nf2)
  }

  /**
   * returns true if the first argument implies the second by the laws of ortholattices.
   */
  def isImplying(formula1: Formula, formula2: Formula): Boolean = {
    val nf1 = computeNormalForm(simplify(formula1))
    val nf2 = computeNormalForm(simplify(formula2))
    latticesLEQ(nf1, nf2)
  }

  def isSubset(s1: Set[Formula], s2: Set[Formula]): Boolean = {
    s1.forall(f1 => s2.exists(g1 => isSame(f1, g1)))
  }
  def isSameSet(s1: Set[Formula], s2: Set[Formula]): Boolean =
    isSubset(s1, s2) && isSubset(s2, s1)

  def isSameSetL(s1: Set[Formula], s2: Set[Formula]): Boolean =
    isSame(ConnectorFormula(And, s1.toSeq), ConnectorFormula(And, s2.toSeq))

  def isSameSetR(s1: Set[Formula], s2: Set[Formula]): Boolean =
    isSame(ConnectorFormula(Or, s2.toSeq), ConnectorFormula(Or, s1.toSeq))

  def contains(s: Set[Formula], f: Formula): Boolean = {
    s.exists(g => isSame(f, g))
  }

  private var totPolarFormula = 0
  sealed abstract class SimpleFormula {
    val uniqueKey: Int = totPolarFormula
    totPolarFormula += 1
    val size: Int
    var inverse: Option[SimpleFormula] = None
    private[EquivalenceChecker] var normalForm: Option[NormalFormula] = None
    def getNormalForm = normalForm
  }
  case class SimplePredicate(id: PredicateLabel, args: Seq[Term], polarity: Boolean) extends SimpleFormula {
    override def toString: String = s"SimplePredicate($id, $args, $polarity)"
    val size = 1
  }
  case class SimpleSchemConnector(id: SchematicConnectorLabel, args: Seq[SimpleFormula], polarity: Boolean) extends SimpleFormula {
    val size = 1
  }
  case class SimpleAnd(children: Seq[SimpleFormula], polarity: Boolean) extends SimpleFormula {
    val size: Int = (children map (_.size)).foldLeft(1) { case (a, b) => a + b }
  }
  case class SimpleForall(x: Identifier, inner: SimpleFormula, polarity: Boolean) extends SimpleFormula {
    val size: Int = 1 + inner.size
  }
  case class SimpleLiteral(polarity: Boolean) extends SimpleFormula {
    val size = 1
    normalForm = Some(NormalLiteral(polarity))
  }

  private var totNormalFormula = 0
  sealed abstract class NormalFormula {
    val uniqueKey: Int = totNormalFormula
    totNormalFormula += 1
    var formulaP: Option[Formula] = None
    var formulaN: Option[Formula] = None
    var formulaAIG: Option[Formula] = None
    var inverse: Option[NormalFormula] = None

    private val lessThanBitSet: mutable.Set[Long] = new mutable.HashSet()
    setLessThanCache(this, true)

    def lessThanCached(other: NormalFormula): Option[Boolean] = {
      val otherIx = 2 * other.uniqueKey
      if (lessThanBitSet.contains(otherIx)) Some(lessThanBitSet.contains(otherIx + 1))
      else None
    }

    def setLessThanCache(other: NormalFormula, value: Boolean): Unit = {
      val otherIx = 2 * other.uniqueKey
      lessThanBitSet.contains(otherIx)
      if (value) lessThanBitSet.update(otherIx + 1, true)
    }

    def recoverFormula: Formula = toFormulaAIG(this)
  }
  sealed abstract class NonTraversable extends NormalFormula
  case class NormalPredicate(id: PredicateLabel, args: Seq[Term], polarity: Boolean) extends NonTraversable {
    override def toString: String = s"NormalPredicate($id, $args, $polarity)"
  }
  case class NormalSchemConnector(id: SchematicConnectorLabel, args: Seq[NormalFormula], polarity: Boolean) extends NonTraversable
  case class NormalAnd(args: Seq[NormalFormula], polarity: Boolean) extends NormalFormula
  case class NormalForall(x: Identifier, inner: NormalFormula, polarity: Boolean) extends NonTraversable
  case class NormalLiteral(polarity: Boolean) extends NormalFormula

  /**
   * Puts back in regular formula syntax, in an AIG (without disjunctions) format
   */
  def toFormulaAIG(f: NormalFormula): Formula =
    if (f.formulaAIG.isDefined) f.formulaAIG.get
    else {
      val r: Formula = f match {
        case NormalPredicate(id, args, polarity) =>
          if (polarity) PredicateFormula(id, args) else ConnectorFormula(Neg, Seq(PredicateFormula(id, args)))
        case NormalSchemConnector(id, args, polarity) =>
          val f = ConnectorFormula(id, args.map(toFormulaAIG))
          if (polarity) f else ConnectorFormula(Neg, Seq(f))
        case NormalAnd(args, polarity) =>
          val f = ConnectorFormula(And, args.map(toFormulaAIG))
          if (polarity) f else ConnectorFormula(Neg, Seq(f))
        case NormalForall(x, inner, polarity) =>
          val f = BinderFormula(Forall, VariableLabel(x), toFormulaAIG(inner))
          if (polarity) f else ConnectorFormula(Neg, Seq(f))
        case NormalLiteral(polarity) => if (polarity) PredicateFormula(top, Seq()) else PredicateFormula(bot, Seq())
      }
      f.formulaAIG = Some(r)
      r
    }

  /**
   * Puts back in regular formula syntax, and performs negation normal form to produce shorter version.
   */
  def toFormulaNNF(f: NormalFormula, positive: Boolean = true): Formula = {
    if (positive){
      if (f.formulaP.isDefined) return f.formulaP.get
      if (f.inverse.isDefined && f.inverse.get.formulaN.isDefined) return f.inverse.get.formulaN.get
    }
    else if (!positive) {
      if (f.formulaN.isDefined) return f.formulaN.get
      if (f.inverse.isDefined && f.inverse.get.formulaP.isDefined) return f.inverse.get.formulaP.get
    }
    val r = f match{
      case NormalPredicate(id, args, polarity) =>
        if (positive==polarity)  PredicateFormula(id, args) else ConnectorFormula(Neg, Seq(PredicateFormula(id, args)))
      case NormalSchemConnector(id, args, polarity) =>
        val f = ConnectorFormula(id, args.map(toFormulaNNF(_, true)))
        if (positive==polarity)  f else ConnectorFormula(Neg, Seq(f))
      case NormalAnd(args, polarity) =>
        if (positive==polarity) 
          ConnectorFormula(And, args.map(c => toFormulaNNF(c, true)))
        else
          ConnectorFormula(Or, args.map(c => toFormulaNNF(c, false)))
      case NormalForall(x, inner, polarity) =>
        if (positive==polarity) 
          BinderFormula(Forall, VariableLabel(x), toFormulaNNF(inner, true))
        else
          BinderFormula(Exists, VariableLabel(x), toFormulaNNF(inner, false))
      case NormalLiteral(polarity) => if (polarity) PredicateFormula(top, Seq()) else PredicateFormula(bot, Seq())
    }
    if (positive) f.formulaP = Some(r)
    else  f.formulaN = Some(r)
    r
  }

  /**
   * Inverse a formula in Polar normal form. Corresponds semantically to taking the negation of the formula.
   */
  def getInversePolar(f: SimpleFormula): SimpleFormula = {
    f.inverse match {
      case Some(value) => value
      case None =>
        val second = f match {
          case f: SimplePredicate => f.copy(polarity = !f.polarity)
          case f: SimpleSchemConnector => f.copy(polarity = !f.polarity)
          case f: SimpleAnd => f.copy(polarity = !f.polarity)
          case f: SimpleForall => f.copy(polarity = !f.polarity)
          case f: SimpleLiteral => f.copy(polarity = !f.polarity)
        }
        f.inverse = Some(second)
        second.inverse = Some(f)
        second
    }
  }

  /**
   * Inverse a formula in Polar normal form. Corresponds semantically to taking the negation of the formula.
   */
  def getInverse(f: NormalFormula): NormalFormula = {
    f.inverse match {
      case Some(value) => value
      case None =>
        val second: NormalFormula = f match {
          case f: NormalPredicate => f.copy(polarity = !f.polarity)
          case f: NormalSchemConnector => f.copy(polarity = !f.polarity)
          case f: NormalAnd => f.copy(polarity = !f.polarity)
          case f: NormalForall => f.copy(polarity = !f.polarity)
          case f: NormalLiteral => f.copy(polarity = !f.polarity)
        }
        f.inverse = Some(second)
        second.inverse = Some(f)
        second
    }
  }

  /**
   * Put a formula in Polar form, which means desugared. In this normal form, the only (non-schematic) symbol is
   * conjunction, the only binder is universal, and negations are flattened
   * @param f The formula that has to be transformed
   * @param polarity If the formula is in a positive or negative context. It is usually true.
   * @return The corresponding PolarFormula
   */
  def polarize(f: Formula, polarity: Boolean): SimpleFormula = {
    if (polarity & f.polarFormula.isDefined) {
      f.polarFormula.get
    } else if (!polarity & f.polarFormula.isDefined) {
      getInversePolar(f.polarFormula.get)
    } else {
      val r = f match {
        case PredicateFormula(label, args) =>
          if (label == top) SimpleLiteral(polarity)
          else if (label == bot) SimpleLiteral(!polarity)
          else SimplePredicate(label, args, polarity)
        case ConnectorFormula(label, args) =>
          label match {
            case cl: ConstantConnectorLabel =>
              cl match {
                case Neg => polarize(args.head, !polarity)
                case Implies => SimpleAnd(Seq(polarize(args(0), true), polarize(args(1), false)), !polarity)
                case Iff =>
                  val l1 = polarize(args(0), true)
                  val r1 = polarize(args(1), true)
                  SimpleAnd(
                    Seq(
                      SimpleAnd(Seq(l1, getInversePolar(r1)), false),
                      SimpleAnd(Seq(getInversePolar(l1), r1), false)
                    ),
                    polarity
                  )
                case And =>
                  SimpleAnd(args.map(polarize(_, true)), polarity)
                case Or => SimpleAnd(args.map(polarize(_, false)), !polarity)
              }
            case scl: SchematicConnectorLabel =>
              SimpleSchemConnector(scl, args.map(polarize(_, true)), polarity)
          }
        case BinderFormula(label, bound, inner) =>
          label match {
            case Forall => SimpleForall(bound.id, polarize(inner, true), polarity)
            case Exists => SimpleForall(bound.id, polarize(inner, false), !polarity)
            case ExistsOne =>
              val y = VariableLabel(freshId(inner.freeVariables.map(_.id), bound.id))
              val c = PredicateFormula(equality, Seq(VariableTerm(bound), VariableTerm(y)))
              val newInner = polarize(ConnectorFormula(Iff, Seq(c, inner)), true)
              SimpleForall(y.id, SimpleForall(bound.id, newInner, false), !polarity)
          }
      }
      if (polarity) f.polarFormula = Some(r)
      else f.polarFormula = Some(getInversePolar(r))
      r
    }
  }

  def toLocallyNameless(t: Term, subst: Map[Identifier, Int], i: Int): Term = {
    t match {
      case Term(label: VariableLabel, _) =>
        if (subst.contains(label.id)) VariableTerm(VariableLabel(Identifier("x", i - subst(label.id))))
        else VariableTerm(VariableLabel(Identifier("$" + label.id.name, label.id.no)))
      case Term(label, args) => Term(label, args.map(c => toLocallyNameless(c, subst, i)))
    }
  }

  def toLocallyNameless(phi: SimpleFormula, subst: Map[Identifier, Int], i: Int): SimpleFormula = {
    phi match {
      case SimplePredicate(id, args, polarity) => SimplePredicate(id, args.map(c => toLocallyNameless(c, subst, i)), polarity)
      case SimpleSchemConnector(id, args, polarity) => SimpleSchemConnector(id, args.map(f => toLocallyNameless(f, subst, i)), polarity)
      case SimpleAnd(children, polarity) => SimpleAnd(children.map(toLocallyNameless(_, subst, i)), polarity)
      case SimpleForall(x, inner, polarity) => SimpleForall(x, toLocallyNameless(inner, subst + (x -> i), i + 1), polarity)
      case SimpleLiteral(polarity) => phi
    }
  }

  def fromLocallyNameless(t: Term, subst: Map[Int, Identifier], i: Int): Term = {

    t match {
      case Term(label: VariableLabel, _) =>
        if (subst.contains(i - label.id.no)) VariableTerm(VariableLabel(subst(i - label.id.no)))
        else if (label.id.name.head == '$') VariableTerm(VariableLabel(Identifier(label.id.name.tail, label.id.no)))
        else {
          throw new Exception("This case should be unreachable, error")
        }
      case Term(label, args) => Term(label, args.map(c => fromLocallyNameless(c, subst, i)))
    }
  }

  def fromLocallyNameless(phi: NormalFormula, subst: Map[Int, Identifier], i: Int): NormalFormula = {
    phi match {
      case NormalPredicate(id, args, polarity) => NormalPredicate(id, args.map(c => fromLocallyNameless(c, subst, i)), polarity)
      case NormalSchemConnector(id, args, polarity) => NormalSchemConnector(id, args.map(f => fromLocallyNameless(f, subst, i)), polarity)
      case NormalAnd(children, polarity) => NormalAnd(children.map(fromLocallyNameless(_, subst, i)), polarity)
      case NormalForall(x, inner, polarity) => NormalForall(x, fromLocallyNameless(inner, subst + (i -> x), i + 1), polarity)
      case NormalLiteral(_) => phi
    }

  }

  def simplify(f: Formula): SimpleFormula = toLocallyNameless(polarize(f, polarity = true), Map.empty, 0)

  def computeNormalForm(formula: SimpleFormula): NormalFormula = {
    formula.normalForm match {
      case Some(value) =>
        value
      case None =>
        val r = formula match {
          case SimplePredicate(id, args, true) =>
            if (id == equality) {
              if (args(0) == args(1))
                NormalLiteral(true)
              else
                NormalPredicate(id, args.sortBy(_.hashCode()), true)
            } else NormalPredicate(id, args, true)
          case SimplePredicate(id, args, false) =>
            getInverse(computeNormalForm(getInversePolar(formula)))
          case SimpleSchemConnector(id, args, true) =>
            NormalSchemConnector(id, args.map(computeNormalForm), true)
          case SimpleSchemConnector(id, args, false) =>
            getInverse(computeNormalForm(getInversePolar(formula)))
          case SimpleAnd(children, polarity) =>
            val newChildren = children map computeNormalForm
            val simp = reduce(newChildren, polarity)
            simp match {
              case conj: NormalAnd if checkForContradiction(conj) =>
                NormalLiteral(!polarity)
              case _ =>
                simp
            }
          case SimpleForall(x, inner, polarity) => NormalForall(x, computeNormalForm(inner), polarity)
          case SimpleLiteral(polarity) => NormalLiteral(polarity)
        }
        formula.normalForm = Some(r)
        r

    }
  }
  def reduceList(children: Seq[NormalFormula], polarity: Boolean): List[NormalFormula] = {
    val nonSimplified = NormalAnd(children, polarity)
    var remaining: Seq[NormalFormula] = Nil
    def treatChild(i: NormalFormula): Seq[NormalFormula] = {
      val r: Seq[NormalFormula] = i match {
        case NormalAnd(ch, true) => ch
        case NormalAnd(ch, false) =>
          if (polarity) {
            val trCh = ch map getInverse
            trCh.find(f => {
              latticesLEQ(nonSimplified, f)
            }) match {
              case Some(value) =>
                treatChild(value)
              case None => List(i)
            }
          } else {
            val trCh = ch
            trCh.find(f => {
              latticesLEQ(f, nonSimplified)
            }) match {
              case Some(value) =>
                treatChild(getInverse(value))
              case None => List(i)
            }
          }
        case _ => List(i)
      }
      r
    }
    children.foreach(i => {
      val r = treatChild(i)
      remaining = r ++ remaining
    })

    var accepted: List[NormalFormula] = Nil
    while (remaining.nonEmpty) {
      val current = remaining.head
      remaining = remaining.tail
      if (!latticesLEQ(NormalAnd(remaining ++ accepted, true), current)) {
        accepted = current :: accepted
      }
    }
    accepted
  }

  def reduce(children: Seq[NormalFormula], polarity: Boolean): NormalFormula = {
    val accepted: List[NormalFormula] = reduceList(children, polarity)
    val r = {
      if (accepted.isEmpty) NormalLiteral(polarity)
      else if (accepted.size == 1)
        if (polarity) accepted.head else getInverse(accepted.head)
      else NormalAnd(accepted, polarity)
    }
    r
  }

  def latticesEQ(formula1: NormalFormula, formula2: NormalFormula): Boolean = latticesLEQ(formula1, formula2) && latticesLEQ(formula2, formula1)

  def latticesLEQ(formula1: NormalFormula, formula2: NormalFormula): Boolean = {
    if (formula1.uniqueKey == formula2.uniqueKey) true
    else
      formula1.lessThanCached(formula2) match {
        case Some(value) => value
        case None =>
          val r = (formula1, formula2) match {
            case (NormalLiteral(b1), NormalLiteral(b2)) => !b1 || b2
            case (NormalLiteral(b), _) => !b
            case (_, NormalLiteral(b)) => b

            case (NormalPredicate(id1, args1, polarity1), NormalPredicate(id2, args2, polarity2)) =>
              id1 == id2 && polarity1 == polarity2 &&
              (args1 == args2 || (id1 == equality && args1(0) == args2(1) && args1(1) == args2(0)))
            case (NormalSchemConnector(id1, args1, polarity1), NormalSchemConnector(id2, args2, polarity2)) =>
              id1 == id2 && polarity1 == polarity2 && args1.zip(args2).forall(f => latticesEQ(f._1, f._2))
            case (NormalForall(x1, inner1, polarity1), NormalForall(x2, inner2, polarity2)) =>
              polarity1 == polarity2 && (if (polarity1) latticesLEQ(inner1, inner2) else latticesLEQ(inner2, inner1))
            case (_: NonTraversable, _: NonTraversable) => false

            case (_, NormalAnd(children, true)) =>
              children.forall(c => latticesLEQ(formula1, c))
            case (NormalAnd(children, false), _) =>
              children.forall(c => latticesLEQ(getInverse(c), formula2))
            case (NormalAnd(children1, true), NormalAnd(children2, false)) =>
              children1.exists(c => latticesLEQ(c, formula2)) || children2.exists(c => latticesLEQ(formula1, getInverse(c)))

            case (nt: NonTraversable, NormalAnd(children, false)) =>
              children.exists(c => latticesLEQ(nt, getInverse(c)))
            case (NormalAnd(children, true), nt: NonTraversable) =>
              children.exists(c => latticesLEQ(c, nt))

          }
          formula1.setLessThanCache(formula2, r)
          r
      }
  }

  def checkForContradiction(f: NormalAnd): Boolean = {
    f match {
      case NormalAnd(children, false) =>
        children.exists(cc => latticesLEQ(cc, f))
      case NormalAnd(children, true) =>
        val shadowChildren = children map getInverse
        shadowChildren.exists(sc => latticesLEQ(f, sc))
    }
  }

  /*

  /**
   * A class that encapsulate "runtime" information of the equivalence checker. It performs memoization for efficiency.
   */
  class LocalEquivalenceChecker2 {

    private val unsugaredVersion = scala.collection.mutable.HashMap[Formula, PolarFormula]()
    // transform a LISA formula into a simpler, desugarised version with less symbols. Conjunction, implication, iff, existsOne are treated as alliases and translated.
    def removeSugar1(phi: Formula): PolarFormula = {
      phi match {
        case PredicateFormula(label, args) =>
          if (label == top) PolarLiteral(true)
          else if (label == bot) PolarLiteral(false)
          else PolarPredicate(label, args.toList)
        case ConnectorFormula(label, args) =>
          label match {
            case Neg => SNeg(removeSugar1(args(0)))
            case Implies =>
              val l = removeSugar1(args(0))
              val r = removeSugar1(args(1))
              PolarAnd(List(SNeg(l), r))
            case Iff =>
              val l = removeSugar1(args(0))
              val r = removeSugar1(args(1))
              val c1 = SNeg(PolarAnd(List(SNeg(l), r)))
              val c2 = SNeg(PolarAnd(List(SNeg(r), l)))
              SNeg(PolarAnd(List(c1, c2)))
            case And =>
              SNeg(SOr(args.map(c => SNeg(removeSugar1(c))).toList))
            case Or => PolarAnd((args map removeSugar1).toList)
            case _ => PolarSchemConnector(label, args.toList.map(removeSugar1))
          }
        case BinderFormula(label, bound, inner) =>
          label match {
            case Forall => PolarForall(bound.id, removeSugar1(inner))
            case Exists => SExists(bound.id, removeSugar1(inner))
            case ExistsOne =>
              val y = VariableLabel(freshId(inner.freeVariables.map(_.id), bound.id))
              val c1 = PolarPredicate(equality, List(VariableTerm(bound), VariableTerm(y)))
              val c2 = removeSugar1(inner)
              val c1_c2 = PolarAnd(List(SNeg(c1), c2))
              val c2_c1 = PolarAnd(List(SNeg(c2), c1))
              SExists(y.id, PolarForall(bound.id, SNeg(PolarAnd(List(SNeg(c1_c2), SNeg(c2_c1))))))
          }
      }
    }

    def toLocallyNameless(t: Term, subst: Map[Identifier, Int], i: Int): Term = {
      t match {
        case Term(label: VariableLabel, _) =>
          if (subst.contains(label.id)) VariableTerm(VariableLabel(Identifier("x", i - subst(label.id))))
          else VariableTerm(VariableLabel(Identifier("$" + label.id.name, label.id.no)))
        case Term(label, args) => Term(label, args.map(c => toLocallyNameless(c, subst, i)))
      }
    }

    def toLocallyNameless(phi: PolarFormula, subst: Map[Identifier, Int], i: Int): PolarFormula = {
      phi match {
        case PolarPredicate(id, args) => PolarPredicate(id, args.map(c => toLocallyNameless(c, subst, i)))
        case PolarSchemConnector(id, args) => PolarSchemConnector(id, args.map(f => toLocallyNameless(f, subst, i)))
        case SNeg(child) => SNeg(toLocallyNameless(child, subst, i))
        case PolarAnd(children) => PolarAnd(children.map(toLocallyNameless(_, subst, i)))
        case PolarForall(x, inner) => PolarForall(Identifier(""), toLocallyNameless(inner, subst + (x -> i), i + 1))
        case SExists(x, inner) => SExists(Identifier(""), toLocallyNameless(inner, subst + (x -> i), i + 1))
        case PolarLiteral(b) => phi
      }
    }

    def removeSugar(phi: Formula): PolarFormula = {
      unsugaredVersion.getOrElseUpdate(phi, toLocallyNameless(removeSugar1(phi), Map.empty, 0))
    }

    private val codesSig: mutable.HashMap[(String, Seq[Int]), Int] = mutable.HashMap()
    codesSig.update(("zero", Nil), 0)
    codesSig.update(("one", Nil), 1)

    val codesTerms: mutable.HashMap[Term, Int] = mutable.HashMap()
    val codesSigTerms: mutable.HashMap[(TermLabel, Seq[Int]), Int] = mutable.HashMap()

    def codesOfTerm(t: Term): Int = codesTerms.getOrElseUpdate(
      t,
      t match {
        case Term(label: VariableLabel, _) =>
          codesSigTerms.getOrElseUpdate((label, Nil), codesSigTerms.size)
        case Term(label, args) =>
          val c = args map codesOfTerm
          codesSigTerms.getOrElseUpdate((label, c), codesSigTerms.size)
      }
    )

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

    def OCBSLCode(phi: PolarFormula): Int = {
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

    def pDisj(phi: PolarFormula, acc: List[NormalFormula]): List[NormalFormula] = {
      if (phi.normalForm.nonEmpty) return pDisjNormal(phi.normalForm.get, acc)
      val r: List[NormalFormula] = phi match {
        case PolarPredicate(label, args) =>
          val lab = label match {
            case _: ConstantPredicateLabel => "cp_" + label.id + "_" + label.arity
            case _: SchematicVarOrPredLabel => "sp_" + label.id + "_" + label.arity
          }
          if (label == top) {
            phi.normalForm = Some(NLiteral(true))
          } else if (label == bot) {
            phi.normalForm = Some(NLiteral(false))
          } else if (label == equality) {
            if (codesOfTerm(args(0)) == codesOfTerm(args(1)))
              phi.normalForm = Some(NLiteral(true))
            else
              phi.normalForm = Some(NormalPredicate(label, args, updateCodesSig((lab, (args map codesOfTerm).sorted))))
          } else {
            phi.normalForm = Some(NormalPredicate(label, args, updateCodesSig((lab, args map codesOfTerm))))
          }
          phi.normalForm.get :: acc
        case PolarSchemConnector(label, args) =>
          val lab = label match {
            case _: ConstantConnectorLabel => "cc_" + label.id + "_" + label.arity
            case _: SchematicConnectorLabel => "sc_" + label.id + "_" + label.arity
          }
          phi.normalForm = Some(NormalConnector(label, args.map(_.normalForm.get), updateCodesSig((lab, args map OCBSLCode))))
          phi.normalForm.get :: acc
        case SNeg(child) => pNeg(child, phi, acc)
        case PolarAnd(children) => children.foldLeft(acc)((p, a) => pDisj(a, p))
        case PolarForall(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NForall(x, inner.normalForm.get, updateCodesSig(("forall", List(r)))))
          phi.normalForm.get :: acc
        case SExists(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NExists(x, inner.normalForm.get, updateCodesSig(("exists", List(r)))))
          phi.normalForm.get :: acc
        case PolarLiteral(true) =>
          phi.normalForm = Some(NLiteral(true))
          phi.normalForm.get :: acc
        case PolarLiteral(false) =>
          phi.normalForm = Some(NLiteral(false))
          phi.normalForm.get :: acc
      }
      r
    }

    def pNeg(phi: PolarFormula, parent: PolarFormula, acc: List[NormalFormula]): List[NormalFormula] = {
      if (phi.normalForm.nonEmpty) return pNegNormal(phi.normalForm.get, parent, acc)
      val r: List[NormalFormula] = phi match {
        case PolarPredicate(label, args) =>
          val lab = label match {
            case _: ConstantPredicateLabel => "cp_" + label.id + "_" + label.arity
            case _: SchematicVarOrPredLabel => "sp_" + label.id + "_" + label.arity
          }
          if (label == top) {
            phi.normalForm = Some(NLiteral(true))
            parent.normalForm = Some(NLiteral(false))
          } else if (label == bot) {
            phi.normalForm = Some(NLiteral(false))
            parent.normalForm = Some(NLiteral(true))
          } else if (label == equality) {
            if (codesOfTerm(args(0)) == codesOfTerm(args(1))) {
              phi.normalForm = Some(NLiteral(true))
              parent.normalForm = Some(NLiteral(false))
            } else {
              phi.normalForm = Some(NormalPredicate(label, args, updateCodesSig((lab, (args map codesOfTerm).sorted))))
              parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
            }
          } else {
            phi.normalForm = Some(NormalPredicate(label, args, updateCodesSig((lab, args map codesOfTerm))))
            parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
            // phi.normalForm = Some(NormalPredicate(id, args, updateCodesSig((lab, args map codesOfTerm))))
          }
          parent.normalForm.get :: acc
        case PolarSchemConnector(label, args) =>
          val lab = label match {
            case _: ConstantConnectorLabel => "cc_" + label.id + "_" + label.arity
            case _: SchematicConnectorLabel => "sc_" + label.id + "_" + label.arity
          }
          phi.normalForm = Some(NormalConnector(label, args.map(_.normalForm.get), updateCodesSig((lab, args map OCBSLCode))))
          parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
          parent.normalForm.get :: acc
        case SNeg(child) => pDisj(child, acc)
        case PolarForall(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NForall(x, inner.normalForm.get, updateCodesSig(("forall", List(r)))))
          parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
          parent.normalForm.get :: acc
        case SExists(x, inner) =>
          val r = OCBSLCode(inner)
          phi.normalForm = Some(NExists(x, inner.normalForm.get, updateCodesSig(("exists", List(r)))))
          parent.normalForm = Some(NNeg(phi.normalForm.get, updateCodesSig(("neg", List(phi.normalForm.get.code)))))
          parent.normalForm.get :: acc
        case PolarLiteral(true) =>
          parent.normalForm = Some(NLiteral(false))
          parent.normalForm.get :: acc
        case PolarLiteral(false) =>
          parent.normalForm = Some(NLiteral(true))
          parent.normalForm.get :: acc
        case PolarAnd(children) =>
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
    def pNegNormal(f: NormalFormula, parent: PolarFormula, acc: List[NormalFormula]): List[NormalFormula] = f match {
      case NNeg(child, c) =>
        pDisjNormal(child, acc)
      case _ =>
        parent.normalForm = Some(NNeg(f, updateCodesSig(("neg", List(f.code)))))
        parent.normalForm.get :: acc
    }

    def check(formula1: Formula, formula2: Formula): Boolean = {
      getCode(formula1) == getCode(formula2)
    }
    def getCode(formula: Formula): Int = OCBSLCode(removeSugar(formula))

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
    def normalForm(phi: Formula): NormalFormula = {
      getCode(phi)
      removeSugar(phi).normalForm.get
    }

  }
  def isSame(term1: Term, term2: Term): Boolean = (new LocalEquivalenceChecker2).isSame(term1, term2)

  def isSame(formula1: Formula, formula2: Formula): Boolean = (new LocalEquivalenceChecker2).isSame(formula1, formula2)

  def isSameSet(s1: Set[Formula], s2: Set[Formula]): Boolean = (new LocalEquivalenceChecker2).isSameSet(s1, s2)

  def isSubset(s1: Set[Formula], s2: Set[Formula]): Boolean = (new LocalEquivalenceChecker2).isSubset(s1, s2)

  def contains(s: Set[Formula], f: Formula): Boolean = (new LocalEquivalenceChecker2).contains(s, f)
   */
}
