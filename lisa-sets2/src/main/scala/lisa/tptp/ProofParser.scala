package lisa.tptp

import leo.datastructures.TPTP.AnnotatedFormula
import leo.datastructures.TPTP.FOF
import leo.datastructures.TPTP.FOFAnnotated
import leo.datastructures.TPTP.FOTAnnotated
import leo.modules.input.{TPTPParser => Parser}
import lisa.utils.K
import K.{repr, -<<, +<<, ->>, +>>, |-}

import java.io.File

import Parser.TPTPParseException
import KernelParser.*
import K.{given}
import lisa.automation.Tautology
import lisa.automation.Tableau

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
    else if f(0).isUpper then
      K.Variable(sanitize(f), K.predicateType(n))
    else throw new Exception(s"Unknown kind of atomic label: $f")
  val mapTerm: ((String, Int) => K.Expression) = (f, n) =>
    val kind = f.head
    val id = f.tail
    if kind == 's' then K.Variable(sanitize(id), K.functionType(n))
    else if kind == 'c' then K.Constant(sanitize(id), K.functionType(n))
    else if f(0).isUpper then
      K.Variable(sanitize(f), K.functionType(n))
    else throw new Exception(s"Unknown kind of term label: $f")
  val mapVariable: (String => K.Variable) = f =>
    if f.head == 'X' then K.Variable(sanitize(f.tail), K.Ind)
    else K.Variable(sanitize(f), K.Ind)


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
    if sequent.left.isEmpty && sequent.right.size == 1 then 
      val formula = sequent.right.head
      return FOFAnnotated(name, role, formulaToFOFStatement(formula), annotations)
    else
      val seq = FOF.Sequent(sequent.left.map(formulaToFOFFormula).toSeq, sequent.right.map(formulaToFOFFormula).toSeq)
      FOFAnnotated(name, role, seq, annotations)
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
    var contextExpr = scala.collection.mutable.Map[String, K.Expression]()
    given defcontext: DefContext = contextExpr.get
    problem.formulas.foreach {
      case ft: FOTAnnotated =>
        if ft.role == "let" then
          val term = ft.formula
          val defedcst = ft.name
          contextExpr(defedcst) = convertTermToKernel(term)(using defcontext)
      case fa: FOFAnnotated =>
        if fa.role == "conjecture" then ()
        else if fa.role == "let" then
          val formula = fa.formula match {
            case FOF.Logical(formula) => formula
            case s: FOF.Sequent => throw new Exception("Sequent in let statement is incorrect")
          }
          val defedcst = fa.name

          contextExpr(defedcst) = convertToKernel(formula)(using defcontext)
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
            annotatedStatementToProofStep(fa, e => nameMap(e)._1, e => nameMap(e)._2, defcontext) match {
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

  def annotatedStatementToProofStep(ann: FOFAnnotated, numbermap: String => Int, sequentmap: String => FOF.Sequent, defctx: DefContext)
      (using maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): Option[(K.SCProofStep, String)] = {
    given (String => Int) = numbermap
    given (String => FOF.Sequent) = sequentmap
    given defcontext: DefContext = defctx
    val r = ann match {
      case Inference.LeftFalse(step, name) => Some((step, name))
      case Inference.Hyp(step, name) => Some((step, name))
      case Inference.LeftWeaken(step, name) => Some((step, name))
      case Inference.RightWeaken(step, name) => Some((step, name))
      case Inference.Cut(step, name) => Some((step, name))
      case Inference.LeftHyp(step, name) => Some((step, name))
      case Inference.LeftNNot(step, name) => Some((step, name))
      case Inference.LeftAnd(step, name) => Some((step, name))
      case Inference.LeftNOr(step, name) => Some((step, name))
      case Inference.LeftNImp(step, name) => Some((step, name))
      case Inference.LeftNAnd(step, name) => Some((step, name))
      case Inference.LeftOr(step, name) => Some((step, name))
      case Inference.LeftImplies(step, name) => Some((step, name))
      case Inference.LeftIff(step, name) => Some((step, name))
      case Inference.LeftNot(step, name) => Some((step, name))
      case Inference.LeftImp2(step, name) => Some((step, name))
      case Inference.LeftNAll(step, name) => Some((step, name))
      case Inference.LeftExists(step, name) => Some((step, name))
      case Inference.LeftForall(step, name) => Some((step, name))
      case Inference.LeftNEx(step, name) => Some((step, name))
      case Inference.RightNot(step, name) => Some((step, name))
      case Inference.RightImplies(step, name) => Some((step, name))
      case Inference.RightIff(step, name) => Some((step, name))
      case Inference.RightOr(step, name) => Some((step, name))
      case Inference.RightAnd(step, name) => Some((step, name))
      case Inference.RightForall(step, name) => Some((step, name))
      case Inference.RightExists(step, name) => Some((step, name))
      case Inference.RightRefl(step, name) => Some((step, name))
      case Inference.RightSubst(step, name) => Some((step, name))
      case Inference.LeftSubst(step, name) => Some((step, name))
      case Inference.RightSubstIff(step, name) => Some((step, name))
      case Inference.LeftSubstIff(step, name) => Some((step, name))
      case Inference.InstFun(step, name) => Some((step, name))
      case Inference.InstPred(step, name) => Some((step, name))
      case Inference.InstMult(step, name) => Some((step, name))
      case Inference.ElimIffRefl(step, name) => Some((step, name))
      case Inference.RightNnf(step, name) => Some((step, name))
      case Inference.Clausify(step, name) => Some((step, name))
      case Inference.RightPrenex(step, name) => Some((step, name))
      case Inference.InstForall(step, name) => Some((step, name))
      case Inference.Res(step, name) => Some((step, name))

      case _ => None
    }
    r
  }

  object Inference {
    import leo.datastructures.TPTP.{Annotations, GeneralTerm, MetaFunctionData, NumberData, Integer, FOF, GeneralFormulaData, FOTData, FOFData}
    import K.apply

    object Tuple {
      def unapply(ann_seq: GeneralTerm): Option[Seq[GeneralTerm]] =
        ann_seq match {
          case GeneralTerm(List(MetaFunctionData("tuple3", tup)), None) => Some(tup)
          case _ => None
        }
    }

    object Number {
      def unapply(ann_seq: GeneralTerm): Option[BigInt] =
        ann_seq match {
          case GeneralTerm(List(NumberData(Integer(n))), None) => Some(n)
          case _ => None
        }
    }
    object Ind {
      def unapply(ann_seq: GeneralTerm)(using defctx: DefContext, maps: MapTriplet): Option[K.Expression] =
        ann_seq match {
          case GeneralTerm(List(GeneralFormulaData(FOTData(term))), None) => Some(convertTermToKernel(term))
          case _ => None
        }
    }
    object Prop {
      def unapply(ann_seq: GeneralTerm)(using defctx: DefContext, maps: MapTriplet): Option[K.Expression] =
      ann_seq match {
        case GeneralTerm(List(GeneralFormulaData(FOFData(FOF.Logical(formula)))), None) => Some(convertToKernel(formula))
        case _ => None
      }
    }
    object String {
      def unapply(ann_seq: GeneralTerm): Option[String] =
        ann_seq match {
          case GeneralTerm(List(MetaFunctionData(string, List())), None) => 
            if string.head == '\'' then Some(string.tail.init)
            else Some(string)
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
    object Sequence {
      def unapply(ann_seq: GeneralTerm): Option[Seq[GeneralTerm]] =
        ann_seq match {
          case GeneralTerm(List(), Some(terms)) => Some(terms)
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
                        GeneralTerm(List(), Some(parameters)), // params
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

    object LeftFalse {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftFalse", Seq(_), Seq()), origin) =>
            Some((K.RestateTrue(convertToKernel(sequent)), name))
          case _ => None
        }
    }

    object Hyp {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("hyp", Seq(_, StrOrNum(n)), Seq()), origin) =>
            Some((K.RestateTrue(convertToKernel(sequent)), name))
          case _ => None
        }
    }

    object Cut {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("cut", Seq(_, StrOrNum(n)), Seq(t1, t2)), origin) =>
            val formula1 = sequentmap(t1).rhs(n.toInt)
            Some((K.Cut(convertToKernel(sequent), numbermap(t1), numbermap(t2), convertToKernel(formula1)), name))
          case _ =>
            None
        }
    }

    object LeftWeaken {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftWeaken", Seq(_, StrOrNum(n)), Seq(t1)), origin) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object RightWeaken {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightWeaken", Seq(_, StrOrNum(n)), Seq(t1)), origin) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object LeftAnd {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftAnd", Seq(_, StrOrNum(n)), Seq(t1)), origin) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object LeftOr {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftOr", Seq(_, StrOrNum(n)), Seq(t1, t2)), origin) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Or(x, y) => (x, y)
              case _ => throw new Exception(s"$name: Expected a disjunction, but got $f")
            }
            Some((K.LeftOr(convertToKernel(sequent), Seq(numbermap(t1), numbermap(t2)), Seq(a, b))), name)
          case _ => None
        }
    }

    object LeftImplies {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftImplies", Seq(_, StrOrNum(n)), Seq(t1, t2)), origin) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Implies(x, y) => (x, y)
              case _ => throw new Exception(s"$name: Expected an implication, but got $f")
            }
            Some((K.LeftImplies(convertToKernel(sequent), numbermap(t1), numbermap(t2), a, b), name))
          case _ => None
        }
    }

    object LeftIff {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftIff", Seq(_, StrOrNum(n)), Seq(t1)), _) =>
            Some(K.Restate(convertToKernel(sequent), numbermap(t1)), name)
          case _ => None
        }
    }

    object LeftNot {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNot", Seq(_, StrOrNum(n)), Seq(t1)), _) =>
            Some(K.Restate(convertToKernel(sequent), numbermap(t1)), name)
          case _ => None
        }
    }

    object LeftExists {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftExists", Seq(_, StrOrNum(n), String(xl)), Seq(t1)), origin) => // x has to be a GeneralTerm representinf a variable, i.e. $fot(x)
            val f = sequent.lhs(n.toInt)
            val x = K.Variable(sanitize(xl), K.Ind)
            val (y: K.Variable, phi: K.Expression) = convertToKernel(f) match {
              case K.Exists(x, phi) => (x, phi)
              case _ => throw new Exception(s"$name: Expected an existential quantification, but got $f")
            }
            if x == y then Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), phi, x), name))
            else Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), K.substituteVariables(phi, Map(y -> x)), x), name))
          case _ => None
        }
    }

    object LeftForall {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftForall", Seq(_, StrOrNum(n), Ind(t)), Seq(t1)), origin) =>
            val f = sequent.lhs(n.toInt)
            val (x, phi) = convertToKernel(f) match {
              case K.Forall(x, phi) => (x, phi)
              case _ => throw new Exception(s"$name: Expected a universal quantification, but got $f")
            }
            println(s"LeftForall: x: ${x.repr}, phi: ${phi.repr}, t: $t")
            Some((K.LeftForall(convertToKernel(sequent), numbermap(t1), phi, x, t), name))
          case _ => None
        }
    }

    object RightAnd {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightAnd", Seq(_, StrOrNum(n)), Seq(t1, t2)), _) =>
            val f = sequent.rhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.And(x, y) => (x, y)
              case _ => throw new Exception(s"$name: Expected a conjunction, but got $f")
            }
            Some((K.RightAnd(convertToKernel(sequent), Seq(numbermap(t1), numbermap(t2)), Seq(a, b)), name))
          case _ => None
        }
    }

    object RightOr {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightOr", Seq(_, StrOrNum(n)), Seq(t1)), _) =>
            val f = sequent.rhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Or(x, y) => (x, y)
              case _ => throw new Exception(s"$name: Expected a disjunction, but got $f")
            }
            Some((K.RightOr(convertToKernel(sequent), numbermap(t1), a, b), name))
          case _ => None
        }
    }

    object RightImplies {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightImplies", Seq(_, StrOrNum(n)), Seq(t1)), _) =>
            val f = sequent.rhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Implies(x, y) => (x, y)
              case _ => throw new Exception(s"$name: Expected an implication, but got $f")
            }
            Some((K.RightImplies(convertToKernel(sequent), numbermap(t1), a, b), name))
          case _ => None
        }
    }

    object RightIff {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightIff", Seq(_, StrOrNum(n)), Seq(t1, t2)), _) =>
            val f = sequent.rhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Iff(x, y) => (x, y)
              case _ => throw new Exception(s"$name: Expected an implication, but got $f")
            }
            Some((K.RightIff(convertToKernel(sequent), numbermap(t1), numbermap(t2), a, b), name))
          case _ => None
        }
    }

 
    object RightNot {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightNot", Seq(_, StrOrNum(n)), Seq(t1)), origin) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object RightExists {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightExists", Seq(_, StrOrNum(n), Ind(t)), Seq(t1)), origin) =>
            val f = sequent.rhs(n.toInt)
            val (x, phi) = convertToKernel(f) match {
              case K.Exists(x, phi) => (x, phi)
              case _ => throw new Exception(s"$name: Expected an existential quantification, but got $f")
            }
            Some((K.RightExists(convertToKernel(sequent), numbermap(t1), phi, x, t), name))
          case _ => None
        }
    }

    object RightForall {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightForall", Seq(_, StrOrNum(n), String(xl)), Seq(t1)), origin) => // x has to be a GeneralTerm representinf a variable, i.e. $fot(x)
            val f = sequent.rhs(n.toInt)
            val x = K.Variable(sanitize(xl), K.Ind)
            val (y: K.Variable, phi: K.Expression) = convertToKernel(f) match {
              case K.Forall(x, phi) => (x, phi)
              case _ => throw new Exception(s"$name: Expected a universal quantification, but got $f")
            }
            if x == y then Some((K.RightForall(convertToKernel(sequent), numbermap(t1), phi, x), name))
            else Some((K.RightForall(convertToKernel(sequent), numbermap(t1), K.substituteVariables(phi, Map(y -> x)), x), name))
          case _ => None
        }
    }

    object RightRefl {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightRefl", Seq(_, StrOrNum(n)), Seq()), origin) =>
            val left = sequent.lhs.map(convertToKernel)
            val right = sequent.rhs.map(convertToKernel)
            val formula = right(n.toInt)
            formula match
              case K.equality(s, t)  if K.isSame(s, t) => Some((K.RightRefl(K.Sequent(left.toSet, right.toSet), formula), name))
              case _ => throw new Exception(s"$name: Expected an equality, but got $formula")
          case _ => None
        }
    }

    object RightSubst {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightSubst", Seq(_, StrOrNum(n), StrOrNum(_), Prop(fl), String(xl)), Seq(t1)), origin) =>
            val f = sequent.lhs(n.toInt)
            val x = K.Variable(sanitize(xl), K.Ind)
            val (s, t) = convertToKernel(f) match {
              case K.equality(s, t) => (s, t)
              case _ => throw new Exception(s"$name: Expected an existential quantification, but got $f")
            }
            Some((K.RightSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(x), fl)), name))
          case _ => None
        }
    }

    object LeftSubst {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftSubst", Seq(_, StrOrNum(n), StrOrNum(_), Prop(fl), String(xl)), Seq(t1)), origin) =>
            val f = sequent.lhs(n.toInt)
            val x = K.Variable(sanitize(xl), K.Ind)
            val (s, t) = convertToKernel(f) match {
              case K.equality(s, t) => (s, t)
              case _ => throw new Exception(s"$name: Expected an existential quantification, but got $f")
            }
            Some((K.LeftSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(x), fl)), name)) 
          case _ => None
        }
    }

    object LeftSubstIff {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftSubstIff", Seq(_, StrOrNum(n), StrOrNum(_), Prop(fl), String(xl)), Seq(t1)), origin) =>
            val f = sequent.lhs(n.toInt)
            val x = K.Variable(sanitize(xl), K.Prop)
            val (s, t) = convertToKernel(f) match {
              case K.iff(s, t) => (s, t)
              case _ => throw new Exception(s"$name: Expected an existential quantification, but got $f")
            }
            Some((K.LeftSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(x), fl)), name)) 
          case _ => None
        }
    }

    object RightSubstIff {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightSubstIff", Seq(_, StrOrNum(n), StrOrNum(_), Prop(fl), String(al)), Seq(t1)), origin) =>
            val f = sequent.lhs(n.toInt)
            val a = K.Variable(al, K.Prop)
            val (s, t) = convertToKernel(f) match {
              case K.iff(s, t) => (s, t)
              case _ => throw new Exception(s"$name: Expected an biimplication, but got $f")
            }
            Some((K.RightSubstEq(convertToKernel(sequent), numbermap(t1), Seq((s, t)), (Seq(a), fl)), name)) 
          case _ => None
        }
    }



    object LeftHyp {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftHyp", Seq(_, StrOrNum(n)), Seq()), origin) =>
            val left = sequent.lhs.map(convertToKernel)
            val formula = left(n.toInt)
            Some((K.RestateTrue(convertToKernel(sequent)), name))
          case _ =>
            None
        }
    }

    object LeftNOr {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotOr", Seq(_, StrOrNum(n)), Seq(t1)), origin) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object LeftNNot {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotNot", Seq(_, StrOrNum(n)), Seq(t1)), origin) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }
    object LeftNImp {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotImplies", Seq(_, StrOrNum(n)), Seq(t1)), origin) =>
            Some((K.Weakening(convertToKernel(sequent), numbermap(t1)), name))
          case _ => None
        }
    }

    object LeftNAnd {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotAnd", Seq(_, StrOrNum(n)), Seq(t1, t2)), origin) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Neg(K.And(x, y)) => (x, y)
              case _ => throw new Exception(s"$name: Expected a negated conjunction, but got $f")
            }
            Some((K.LeftOr(convertToKernel(sequent), Seq(numbermap(t1), numbermap(t2)), Seq(K.neg(a), K.neg(b))), name))
          case _ => None
        }
    }
    object LeftImp2 {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftImp2", Seq(_, StrOrNum(n)), Seq(t1, t2)), origin) =>
            val f = sequent.lhs(n.toInt)
            val (a, b) = convertToKernel(f) match {
              case K.Implies(x, y) => (x, y)
              case _ => throw new Exception(s"$name: Expected an implication, but got $f")
            }
            Some((K.LeftOr(convertToKernel(sequent), Seq(numbermap(t1), numbermap(t2)), Seq(K.neg(a), b)), name))
          case _ => None
        }
    }

    object LeftNAll {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotAll", Seq(_, StrOrNum(n), String(xl)), Seq(t1)), origin) => // x has to be a GeneralTerm representinf a variable, i.e. $fot(x)
            val f = sequent.lhs(n.toInt)
            val x = K.Variable(sanitize(xl), K.Ind)
            val (y: K.Variable, phi: K.Expression) = convertToKernel(f) match {
              case K.Neg(K.forall(K.Lambda(x, phi))) => (x, phi)
              case _ => throw new Exception(s"$name: Expected a universal quantification, but got $f")
            }
            println(s"y: $y")
            println(s"x: $x")
            if x == y then Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), K.neg(phi), x), name))
            else 
              Some((K.LeftExists(convertToKernel(sequent), numbermap(t1), K.substituteVariables(K.neg(phi), Map(y -> x)), x), name))
          case _ => None
        }
    }
    object LeftNEx {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("leftNotEx", Seq(_, StrOrNum(n), Ind(t)), Seq(t1)), origin) =>
            val f = sequent.lhs(n.toInt)
            val (x, phi) = convertToKernel(f) match {
              case K.Neg(K.Exists(x, phi)) => (x, phi)
              case _ => throw new Exception(s"$name: Expected a negated existential quantification, but got $f")
            }
            Some((K.LeftForall(convertToKernel(sequent), numbermap(t1), K.neg(phi), x, t), name))
          case _ => None
        }
    }

    object InstFun {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("instFun", Seq(_, String(sfl), Ind(t), Sequence(varsl)), Seq(t1)), origin) =>
            val vars = varsl.map {
              case String(xl) => K.Variable(sanitize(xl), K.Ind)
              case _ => throw new Exception(s"$name: Expected a list of strings, but got $varsl")
            }
            val sf = K.Variable(sfl, K.functionType(vars.size))
            val seq = convertToKernel(sequent)
            val prem = convertToKernel(sequentmap(t1))
            Some((K.InstSchema(seq, numbermap(t1), Map(sf -> K.lambda(vars, t))), name))
          case _ => None
        }
    }

    object InstPred {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("instPred", Seq(_, String(sfl), Prop(phi), Sequence(varsl)), Seq(t1)), origin) =>
            val vars = varsl.map {
              case String(xl) => K.Variable(sanitize(xl), K.Ind)
              case _ => throw new Exception(s"$name: Expected a list of strings, but got $varsl")
            }
            val sp = K.Variable(sfl, K.predicateType(vars.size))
            val seq = convertToKernel(sequent)
            Some((K.InstSchema(seq, numbermap(t1), Map(sp -> K.lambda(vars, phi))), name))
          case _ => None
        }
    }

    object InstMult {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("instMult", Seq(_, Sequence(instantiations)), Seq(t1)), origin) =>
            val map = instantiations.map {
              case Tuple(Seq(String(sfl), expr, Sequence(varsl))) =>
                val vars = varsl.map {
                  case String(xl) => K.Variable(sanitize(xl), K.Ind)
                  case _ => throw new Exception(s"$name: Expected a list of strings, but got $varsl")
                }
                expr match
                  case Ind(t) => 
                    val sf = K.Variable(sfl, K.functionType(vars.size))
                    sf -> K.lambda(vars, t)
                  case Prop(phi) => 
                    val sp = K.Variable(sfl, K.predicateType(vars.size))
                    sp -> K.lambda(vars, phi)
              }.toMap
            val seq = convertToKernel(sequent)
            Some((K.InstSchema(seq, numbermap(t1), map), name))
          case _ => None
        }
    }
    object Clausify {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("clausify", Seq(_, StrOrNum(n)), Seq()), origin) =>
            val seq = convertToKernel(sequent)
            Tautology.solveSequent(seq) match
              case Left(proof) => Some((K.SCSubproof(proof), name))
              case Right(msg, seq) => throw new Exception(s"Failed to justify clausify inference for sequent step ${name} with sequent ${seq.repr}: $msg")
          case _ => None
        }
    }

    object ElimIffRefl {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("elimIffRefl", Seq(_, StrOrNum(_)), Seq(t1)), origin) =>
            val seq = convertToKernel(sequent)
            Some((K.Weakening(seq, numbermap(t1)), name))
          case _ => None
        }
    }

    object RightNnf {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightNnf", Seq(_, StrOrNum(_), StrOrNum(_)), Seq(t1)), origin) =>
            val seq = convertToKernel(sequent)
            Some((K.Weakening(seq, numbermap(t1)), name))
          case _ => None
        }
    }

    object RightPrenex {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("rightPrenex", Seq(_, StrOrNum(n), StrOrNum(m)), Seq(t1)), origin) =>
            val seq = convertToKernel(sequent)
            val prem = sequentmap(t1)
            val formula1 = convertToKernel(prem.rhs(n.toInt))
            val formula2 = convertToKernel(sequent.rhs(m.toInt))
            Tableau.solve(formula1 |- formula2) match
              case Some(proof) => 
                val steps = proof.steps
                val last = K.Cut(seq, -1, steps.size-1, formula1)
                Some((K.SCSubproof(K.SCProof(steps :+ last, IndexedSeq(convertToKernel(prem))), IndexedSeq(numbermap(t1))), name))
              case None => throw new Exception(s"Failed to justify prenex inference for sequent ${seq.repr}")
          case _ => None
        }
    }

    object InstForall {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("instForall", Seq(_, StrOrNum(n), Ind(t)), Seq(t1)), origin) =>
            val seq = convertToKernel(sequent)
            val prem = sequentmap(t1)
            val formula = convertToKernel(prem.rhs(n.toInt))
            formula match {
              case r @ K.Application(K.forall, K.Lambda(x, f)) =>
                val newf = K.substituteVariables(f, Map(x -> t))
                val s0 = K.Hypothesis((newf |- newf), newf)
                val s1 = K.LeftForall((r |- newf), 0, f, x, t)
                val s2 = K.Cut(seq +>> newf, -1, 1, r)
                Some((K.SCSubproof(K.SCProof(IndexedSeq(s0, s1, s2), IndexedSeq(convertToKernel(sequentmap(t1)))), Seq(numbermap(t1))), name))
              case _ => throw new IllegalArgumentException(s"InstForall: Expected a universal quantification, but got ${formula.repr}")
            }
          case _ => None
        }
    }

    object Res {
      def unapply(ann_seq: FOFAnnotated)(using defctx: DefContext,
          numbermap: String => Int,
          sequentmap: String => FOF.Sequent
      )(using maps: MapTriplet): Option[(K.SCProofStep, String)] =
        ann_seq match {
          case FOFAnnotated(name, role, sequent: FOF.Sequent, Inference("res", Seq(_, StrOrNum(n)), Seq(t1, t2)), origin) =>
            val seq = convertToKernel(sequent)
            val seqt1 = convertToKernel(sequentmap(t1))
            val seqt2 = convertToKernel(sequentmap(t2))
            val formula1 = convertToKernel(sequentmap(t1).rhs(n.toInt))
            val seqint = seqt2 +<< formula1 ->> K.!(formula1)
            val subproof = K.SCProof(IndexedSeq(K.Restate(seqint, -2), K.Cut(seq, -1, 0, formula1)), IndexedSeq(seqt1, seqt2))
            val step = K.SCSubproof(subproof, IndexedSeq(numbermap(t1), numbermap(t2)))
            Some((step, name))
          case _ => None
        }
    }


  }
}
