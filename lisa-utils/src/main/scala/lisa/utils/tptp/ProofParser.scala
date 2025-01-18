package lisa.utils.tptp

import leo.datastructures.TPTP.AnnotatedFormula
import leo.datastructures.TPTP.FOF
import leo.datastructures.TPTP.FOFAnnotated
import leo.modules.input.{TPTPParser => Parser}
import lisa.utils.K
import K.repr

import java.io.File

import Parser.TPTPParseException
import KernelParser.*
import K.{given}

object ProofParser {
  val TPTPversion = "TPTP v8.0.0"
  val rand = scala.util.Random()

  type MapTriplet = ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)

  val mapAtom: ((String, Int) => K.Expression) = (f, n) =>
    val kind = f.head
    val id = f.tail
    if kind == 's' then
      K.Variable(sanitize(id), K.predicateType(n))
    else if kind == 'c' then K.Constant(sanitize(id), K.predicateType(n))
    else throw new Exception(s"Unknown kind of atomic label: $f")
  val mapTerm: ((String, Int) => K.Expression) = (f, n) =>
    val kind = f.head
    val id = f.tail
    if kind == 's' then K.Variable(sanitize(id), K.functionType(n))
    else if kind == 'c' then K.Constant(sanitize(id), K.functionType(n))
    else throw new Exception(s"Unknown kind of term label: $f")
  val mapVariable: (String => K.Variable) = f =>
    if f.head == 'X' then K.Variable(f.tail, K.Ind)
    else K.Variable(f, K.Ind)

  given maps: MapTriplet = (mapAtom, mapTerm, mapVariable)

  def problemToFile(fileDirectory: String, fileName: String, name: String, axioms: Seq[K.Sequent], conjecture: K.Sequent, source: String): File = {
    // case class Problem(file: String, domain: String, name: String, status: String, spc: Seq[String], formulas: Seq[AnnotatedStatement])
    val number = rand.nextInt(1000)
    val file = new File(fileDirectory + fileName + ".p")
    // val fileName = originFile.split("/").last
    val header =
      s"""%--------------------------------------------------------------------------
% File     : $fileName : $TPTPversion.
% Domain   : None
% Problem  : ${name}
% Version  : None
% English  :

% Refs     : https://github.com/epfl-lara/lisa
%          : lisa.utils.tptp.ProofParser
% Source   : [Lisa, $source]
% Names    : 

% Status   : Unknown
% Rating   : ?
% Syntax   : ?
% SPC      : FOF_UNK_RFO_SEQ

% Comments : This problem, was printed from a statement in a proof of a theorem by the Lisa theorem prover for submission to proof-producing ATPs.
%--------------------------------------------------------------------------
"""
    val writer = new java.io.PrintWriter(file)
    writer.write(header)
    var counter = 0
    def nextc = { counter += 1; counter }
    axioms.foreach(s => writer.write(sequentToFOFAnnotated(s, "a" + nextc, "axiom").pretty + "\n"))
    writer.write(sequentToFOFAnnotated(conjecture, "c" + nextc, "conjecture").pretty + "\n\n")
    writer.close()
    file
  }

  def sequentToFOFAnnotated(sequent: K.Sequent, name: String, role: String): FOFAnnotated = {
    val annotations = None
    val formula = K.sequentToFormula(sequent)
    FOFAnnotated(name, role, formulaToFOFStatement(formula), annotations)
  }

  def isLowerWord(s: String): Boolean = s.head.isLower && s.tail.forall(_.isLetterOrDigit)
  inline def quoted(s: String): String = if isLowerWord(s) then s else s"'$s'"

  def termToFOFTerm(term: K.Expression): FOF.Term = {
    term match {
      case K.Variable(id, K.Ind) => FOF.Variable("X" + id)
      case K.Constant(id, K.Ind) => FOF.AtomicTerm(quoted("c" + id), Seq())
      case K.Multiapp(K.Constant(id, typ), args) =>
        FOF.AtomicTerm(quoted("c" + id), args.map(termToFOFTerm))
      case K.Multiapp(K.Variable(id, typ), args) =>
        FOF.AtomicTerm(quoted("s" + id), args.map(termToFOFTerm))
      case K.Epsilon(v, f) => throw new Exception("Epsilon terms are not supported")
      case _ => throw new Exception("The expression is not purely first order")
    }
  }
  def formulaToFOFFormula(formula: K.Expression): FOF.Formula = {
    formula match
      case K.equality(left, right) =>
        FOF.Equality(termToFOFTerm(left), termToFOFTerm(right))
      case K.top => FOF.AtomicFormula("$true", Seq())
      case K.bot => FOF.AtomicFormula("$false", Seq())
      case K.neg(f) => FOF.UnaryFormula(FOF.~, formulaToFOFFormula(f))
      case K.and(f1, f2) => FOF.BinaryFormula(FOF.&, formulaToFOFFormula(f1), formulaToFOFFormula(f2))
      case K.or(f1, f2) => FOF.BinaryFormula(FOF.|, formulaToFOFFormula(f1), formulaToFOFFormula(f2))
      case K.implies(f1, f2) => FOF.BinaryFormula(FOF.Impl, formulaToFOFFormula(f1), formulaToFOFFormula(f2))
      case K.iff(f1, f2) => FOF.BinaryFormula(FOF.<=>, formulaToFOFFormula(f1), formulaToFOFFormula(f2))
      case K.forall(K.Lambda(v, f)) => FOF.QuantifiedFormula(FOF.!, Seq("X" + v.id), formulaToFOFFormula(f))
      case K.exists(K.Lambda(v, f)) => FOF.QuantifiedFormula(FOF.?, Seq("X" + v.id), formulaToFOFFormula(f))
      case K.forall(p) =>
        val x = K.freshId(p.freeVariables.map(_.id), "x")
        FOF.QuantifiedFormula(FOF.!, Seq("X" + x), formulaToFOFFormula(K.Application(p, K.Variable(x, K.Ind))))
      case K.exists(p) =>
        val x = K.freshId(p.freeVariables.map(_.id), "x")
        FOF.QuantifiedFormula(FOF.?, Seq("X" + x), formulaToFOFFormula(K.Application(p, K.Variable(x, K.Ind))))
      case K.Multiapp(K.Constant(id, typ), args) =>
        FOF.AtomicFormula(quoted("c" + id), args.map(termToFOFTerm))
      case K.Multiapp(K.Variable(id, typ), args) =>
        FOF.AtomicFormula(quoted("s" + id), args.map(termToFOFTerm))
      case _ => throw new Exception("The expression is not purely first order: " + formula)
        
  }

  def formulaToFOFStatement(formula: K.Expression): FOF.Statement = {
    FOF.Logical(formulaToFOFFormula(formula))
  }

  def reconstructProof(file: File)(using maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.SCProof = {
    val problem = Parser.problem(io.Source.fromFile(file))
    val nameMap = scala.collection.mutable.Map[String, (Int, FOF.Sequent)]()
    var prems = List[K.Sequent]()
    var steps = List[K.SCProofStep]()
    var numberSteps = 0
    problem.formulas.foreach {
      case fa: FOFAnnotated =>
        if fa.role == "conjecture" then ()
        else
          val fofsequent = fa.formula match {
            case FOF.Logical(formula) => FOF.Sequent(Seq(), Seq(formula))
            case s: FOF.Sequent => s
          }
          if fa.role == "axiom" then
            val sequent = K.Sequent(fofsequent.lhs.map(convertToKernel).toSet, fofsequent.rhs.map(convertToKernel).toSet)
            nameMap(fa.name) = (-prems.size - 1, fofsequent)
            prems = sequent :: prems
          else
            annotatedStatementToProofStep(fa, e => nameMap(e)._1, e => nameMap(e)._2) match {
              case Some((step, name)) =>
                nameMap(name) = (numberSteps, fofsequent)
                numberSteps += 1
                steps = step :: steps
              case None => throw new Exception(s"Proof step could not be reconstructed from ${fa.pretty}")
            }
      case _ => throw new Exception("Only FOF statements are supported")
    }
    K.SCProof(steps.reverse.toIndexedSeq, prems.reverse.toIndexedSeq)
  }

  def annotatedStatementToProofStep(ann: FOFAnnotated, numbermap: String => Int, sequentmap: String => FOF.Sequent)
      (using maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): Option[(K.SCProofStep, String)] = {
    given (String => Int) = numbermap
    given (String => FOF.Sequent) = sequentmap
    val r = ann match {
      case Inference.Hypothesis(step, name) => Some((step, name))
      case Inference.Cut(step, name) => Some((step, name))
      case Inference.LeftHypothesis(step, name) =>
        Some((step, name))
      case Inference.LeftNNot(step, name) => Some((step, name))
      case Inference.LeftAnd(step, name) => Some((step, name))
      case Inference.LeftNOr(step, name) => Some((step, name))
      case Inference.LeftNImp(step, name) => Some((step, name))
      case Inference.LeftNAnd(step, name) => Some((step, name))
      case Inference.LeftOr(step, name) => Some((step, name))
      case Inference.LeftImp1(step, name) => Some((step, name))
      case Inference.LeftImp2(step, name) => Some((step, name))
      case Inference.LeftNAll(step, name) => Some((step, name))
      case Inference.LeftEx(step, name) => Some((step, name))
      case Inference.LeftAll(step, name) => Some((step, name))
      case Inference.LeftNEx(step, name) => Some((step, name))
      case Inference.RightNot(step, name) => Some((step, name))
      case Inference.RightRefl(step, name) => Some((step, name))
      case Inference.RightSubstEq(step, name) => Some((step, name))
      case Inference.LeftSubstEq(step, name) => Some((step, name))
      case Inference.RightSubstIff(step, name) => Some((step, name))
      case Inference.LeftSubstIff(step, name) => Some((step, name))
      case _ => None
    }
    r
  }

  object Inference {
    import leo.datastructures.TPTP.{Annotations, GeneralTerm, MetaFunctionData, NumberData, Integer, FOF, GeneralFormulaData, FOTData, FOFData}
    import K.apply

    object Number {
      def unapply(ann_seq: GeneralTerm): Option[BigInt] =
        ann_seq match {
          case GeneralTerm(List(NumberData(Integer(n))), None) => Some(n)
          case _ => None
        }
    }
    object Ind {
      def unapply(ann_seq: GeneralTerm)(using maps: MapTriplet): Option[K.Expression] =
        ann_seq match {
          case GeneralTerm(List(GeneralFormulaData(FOTData(term))), None) => Some(convertTermToKernel(term))
          case _ => None
        }
    }
    object Prop {
      def unapply(ann_seq: GeneralTerm)(using maps: MapTriplet): Option[K.Expression] =
      ann_seq match {
        case GeneralTerm(List(GeneralFormulaData(FOFData(FOF.Logical(formula)))), None) => Some(convertToKernel(formula))
        case _ => None
      }
    }
    object String {
      def unapply(ann_seq: GeneralTerm): Option[String] =
        ann_seq match {
          case GeneralTerm(List(MetaFunctionData(string, List())), None) => Some(string)
          case _ => None
        }
    }
    object StrOrNum {
      def unapply(ann_seq: GeneralTerm): Option[String] =
        ann_seq match {
          case String(s) => Some(s)
          case Number(n) => Some(n.toString)
          case _ => None
        }
    }
    def unapply(ann_seq: Annotations): Option[(String, Seq[GeneralTerm], Seq[String])] =
      ann_seq match {
        case Some(
              (
                GeneralTerm(
                  List(
                    MetaFunctionData(
                      "inference",
                      List(
                        GeneralTerm(List(MetaFunctionData(stepName, List())), None), // stepnames
                        GeneralTerm(List(MetaFunctionData("param", parameters)), None), // params
                        GeneralTerm(List(), Some(numberTerms))
                      ) // numbers
                    )
                  ),
                  None
                ),
                None
              )
            ) =>
          Some(
            (
              stepName,
              parameters,
              numberTerms.map {
                case StrOrNum(n) => n.toString
                case String(n) => n
                case _ => throw new Exception(s"Expected a list of number as last parameter of inference, but got $numberTerms")
              }
            )
          )
        case _ => None
      }

    object Hypothesis {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("hyp", Seq(StrOrNum(n), StrOrNum(m)), Seq())) =>
            if (sequent.lhs(n.toInt) == sequent.rhs(m.toInt)) then
              val left = sequent.lhs.map(convertToKernel)
              val right = sequent.rhs.map(convertToKernel)
              Some((K.RestateTrue(K.Sequent(left.toSet, right.toSet)), name))
            else None
          case _ => None
        }
    } // List(GeneralTerm(List(),Some(List(GeneralTerm(List(NumberData(Integer(6))),None), GeneralTerm(List(NumberData(Integer(5))),None)))))

    object Cut {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("cut", Seq(StrOrNum(n), StrOrNum(m)), Seq(t1, t2))) =>
            val formula1 = sequentmap(t1).rhs(n.toInt)
            val formula2 = sequentmap(t2).lhs(m.toInt)
            if (formula1 == formula2) then Some((K.Cut(convertToKernel(sequent), numbermap(t1), numbermap(t2), convertToKernel(formula1)), name))
            else throw new Exception(s"Cut inference with different formulas given in the premises")
          case _ =>
            None
        }

    }

    object LeftHypothesis {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftHyp", Seq(StrOrNum(n), StrOrNum(m)), Seq())) =>
            val left = sequent.lhs.map(convertToKernel)
            val right = sequent.rhs.map(convertToKernel)
            val formula = left(n.toInt)
            if (formula == K.neg(left(m.toInt)) || K.neg(formula) == left(m.toInt)) then Some((K.RestateTrue(K.Sequent(left.toSet, right.toSet)), name))
            else None
          case _ =>
            None
        }
    }
    object LeftNNot {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotNot", Seq(StrOrNum(n)), Seq(t1))) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }
    object LeftAnd {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftAnd", Seq(StrOrNum(n)), Seq(t1))) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }
    object LeftNOr {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotOr", Seq(StrOrNum(n)), Seq(t1))) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }
    object LeftNImp {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotImp", Seq(StrOrNum(n)), Seq(t1))) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object LeftNAnd {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotAnd", Seq(StrOrNum(n)), Seq(t1, t2))) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Neg(K.And(x, y)) => (x, y)
              case _ => throw new Exception(s"Expected a negated conjunction, but got $f")
            }
            Some((K.LeftOr(convertToKernel(sequent), Seq(numbermap(t1), numbermap(t2)), Seq(K.neg(a), K.neg(b))), name))
          case _ => None
        }
    }

    object LeftOr {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftOr", Seq(StrOrNum(n)), Seq(t1, t2))) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Or(x, y) => (x, y)
              case _ => throw new Exception(s"Expected a disjunction, but got $f")
            }
            Some((K.LeftOr(convertToKernel(sequent), Seq(numbermap(t1), numbermap(t2)), Seq(a, b))), name)
          case _ => None
        }
    }

    object LeftImp1 {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftImp1", Seq(StrOrNum(n)), Seq(t1, t2))) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Implies(x, y) => (x, y)
              case _ => throw new Exception(s"Expected an implication, but got $f")
            }
            Some((K.LeftImplies(convertToKernel(sequent), numbermap(t1), numbermap(t2), a, b), name))
          case _ => None
        }
    }

    object LeftImp2 {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftImp2", Seq(StrOrNum(n)), Seq(t1, t2))) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Implies(x, y) => (x, y)
              case _ => throw new Exception(s"Expected an implication, but got $f")
            }
            Some((K.LeftOr(convertToKernel(sequent), Seq(numbermap(t1), numbermap(t2)), Seq(K.neg(a), b)), name))
          case _ => None
        }
    }

    object LeftNAll {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotForall", Seq(StrOrNum(n), Ind(xl)), Seq(t1))) => // x has to be a GeneralTerm representinf a variable, i.e. $fot(x)
            val f = sequent.lhs(n.toInt)
            val x = xl match
              case x: K.Variable => x
              case _ => throw new Exception(s"Expected a variable, but got $xl")
            val (y: K.Variable, phi: K.Expression) = convertToKernel(f) match {
              case K.Neg(K.forall(K.Lambda(x, phi))) => (x, phi)
              case _ => throw new Exception(s"Expected a universal quantification, but got $f")
            }
            if x == y then Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), phi, x), name))
            else Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), K.substituteVariables(K.neg(phi), Map(y -> xl)), x), name))
          case _ => None
        }
    }

    object LeftEx {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftEx", Seq(StrOrNum(n), Ind(xl)), Seq(t1))) => // x has to be a GeneralTerm representinf a variable, i.e. $fot(x)
            val f = sequent.lhs(n.toInt)
            val x = xl match
              case x:K.Variable => x
              case _ => throw new Exception(s"Expected a variable, but got $xl")
            val (y: K.Variable, phi: K.Expression) = convertToKernel(f) match {
              case K.Exists(x, phi) => (x, phi)
              case _ => throw new Exception(s"Expected an existential quantification, but got $f")
            }
            if x == y then Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), phi, x), name))
            else Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), K.substituteVariables(phi, Map(y -> xl)), x), name))
          case _ => None
        }
    }

    object LeftAll {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftForall", Seq(StrOrNum(n), Ind(t)), Seq(t1))) =>
            val f = sequent.lhs(n.toInt)
            val (x, phi) = convertToKernel(f) match {
              case K.Forall(x, phi) => (x, phi)
              case _ => throw new Exception(s"Expected a universal quantification, but got $f")
            }
            Some((K.LeftForall(convertToKernel(sequent), numbermap(t1), phi, x, t), name))
          case _ => None
        }
    }

    object LeftNEx {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotEx", Seq(StrOrNum(n), Ind(t)), Seq(t1))) =>
            val f = sequent.lhs(n.toInt)
            val (x, phi) = convertToKernel(f) match {
              case K.Neg(K.Exists(x, phi)) => (x, phi)
              case _ => throw new Exception(s"Expected a negated existential quantification, but got $f")
            }
            Some((K.LeftForall(convertToKernel(sequent), numbermap(t1), K.neg(phi), x, t), name))
          case _ => None
        }
    }

    object RightNot {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightNot", Seq(StrOrNum(n)), Seq(t1))) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object RightRefl {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightRefl", Seq(StrOrNum(n)), Seq())) =>
            val left = sequent.lhs.map(convertToKernel)
            val right = sequent.rhs.map(convertToKernel)
            val formula = right(n.toInt)
            formula match
              case K.equality(s, t)  if K.isSame(s, t) => Some((K.RightRefl(K.Sequent(left.toSet, right.toSet), formula), name))
              case _ => throw new Exception(s"Expected an equality, but got $formula")
          case _ => None
        }
    }

    object RightSubstEq {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightSubstEq", Seq(StrOrNum(n), Prop(fl), Ind(xl)), Seq(t1))) =>
            val f = sequent.lhs(n.toInt)
            val x = xl match
              case x:K.Variable => x
              case _ => throw new Exception(s"Expected a variable, but got $xl")
            val (s, t) = convertToKernel(f) match {
              case K.equality(s, t) => (s, t)
              case _ => throw new Exception(s"Expected an existential quantification, but got $f")
            }
            Some((K.RightSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(x), fl)), name))

          case _ => None
        }
    }

    object LeftSubstEq {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftSubstEq", Seq(StrOrNum(n), Prop(fl), Ind(xl)), Seq(t1))) =>
            val f = sequent.lhs(n.toInt)
            val x = xl match
              case x:K.Variable => x
              case _ => throw new Exception(s"Expected a variable, but got $xl")
            val (s, t) = convertToKernel(f) match {
              case K.equality(s, t) => (s, t)
              case _ => throw new Exception(s"Expected an existential quantification, but got $f")
            }
            Some((K.LeftSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(x), fl)), name)) 
          case _ => None
        }
    }

    object LeftSubstIff {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftSubstIff", Seq(StrOrNum(n), Prop(fl), Prop(xl)), Seq(t1))) =>
            val f = sequent.lhs(n.toInt)
            val x = xl match
              case x:K.Variable => x
              case _ => throw new Exception(s"Expected a variable, but got $xl")
            val (s, t) = convertToKernel(f) match {
              case K.iff(s, t) => (s, t)
              case _ => throw new Exception(s"Expected an existential quantification, but got $f")
            }
            Some((K.LeftSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(x), fl)), name)) 
          case _ => None
        }
    }

    object RightSubstIff {
      def unapply(ann_seq: FOFAnnotated)(using
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightSubstIff", Seq(StrOrNum(n), Prop(fl), Prop(xl)), Seq(t1))) =>
            val f = sequent.lhs(n.toInt)
            val x = xl match
              case x:K.Variable => x
              case _ => throw new Exception(s"Expected a variable, but got $xl")
            val (s, t) = convertToKernel(f) match {
              case K.iff(s, t) => (s, t)
              case _ => throw new Exception(s"Expected an existential quantification, but got $f")
            }
            Some((K.RightSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(x), fl)), name)) 
          case _ => None
        }
    }

  }
}
