package lisa.tptp

import leo.datastructures.TPTP
import leo.datastructures.TPTP.CNF
import leo.datastructures.TPTP.FOF
import leo.modules.input.TPTPParser as Parser
import lisa.kernel.fol.FOL as K
import lisa.kernel.proof.SequentCalculus as LK
import lisa.tptp.*
import lisa.utils.Helpers.*

import java.io.File
import scala.util.matching.Regex

import Parser.TPTPParseException

object KernelParser {

  private case class ProblemMetadata(file: String, domain: String, problem: String, status: String, spc: Seq[String])

  /**
   * @param formula A formula in the tptp language
   * @return the corresponding LISA formula
   */
  def parseToKernel(formula: String): K.Formula = convertToKernel(Parser.fof(formula))

  /**
   * @param formula a tptp formula in leo parser
   * @return the same formula in LISA
   */
  def convertToKernel(formula: FOF.Formula): K.Formula = {
    formula match {
      case FOF.AtomicFormula(f, args) => K.PredicateFormula(K.ConstantPredicateLabel(f, args.size), args map convertTermToKernel)
      case FOF.QuantifiedFormula(quantifier, variableList, body) =>
        quantifier match {
          case FOF.! => variableList.foldRight(convertToKernel(body))((s, f) => K.Forall(K.VariableLabel(s), f))
          case FOF.? => variableList.foldRight(convertToKernel(body))((s, f) => K.Exists(K.VariableLabel(s), f))
        }
      case FOF.UnaryFormula(connective, body) =>
        connective match {
          case FOF.~ => K.Neg(convertToKernel(body))
        }
      case FOF.BinaryFormula(connective, left, right) =>
        connective match {
          case FOF.<=> => convertToKernel(left) <=> convertToKernel(right)
          case FOF.Impl => convertToKernel(left) ==> convertToKernel(right)
          case FOF.<= => convertToKernel(right) ==> convertToKernel(left)
          case FOF.<~> => !(convertToKernel(left) <=> convertToKernel(right))
          case FOF.~| => !(convertToKernel(left) \/ convertToKernel(right))
          case FOF.~& => !(convertToKernel(left) /\ convertToKernel(right))
          case FOF.| => convertToKernel(left) \/ convertToKernel(right)
          case FOF.& => convertToKernel(left) /\ convertToKernel(right)
        }
      case FOF.Equality(left, right) => K.equality(convertTermToKernel(left), convertTermToKernel(right))
      case FOF.Inequality(left, right) => !K.equality(convertTermToKernel(left), convertTermToKernel(right))
    }
  }

  def convertToKernel(formula: CNF.Formula): K.Formula = {

    K.ConnectorFormula(
      K.Or,
      formula.map {
        case CNF.PositiveAtomic(formula) => K.PredicateFormula(K.ConstantPredicateLabel(formula.f, formula.args.size), formula.args.map(convertTermToKernel).toList)
        case CNF.NegativeAtomic(formula) => !K.PredicateFormula(K.ConstantPredicateLabel(formula.f, formula.args.size), formula.args.map(convertTermToKernel).toList)
        case CNF.Equality(left, right) => K.equality(convertTermToKernel(left), convertTermToKernel(right))
        case CNF.Inequality(left, right) => !K.equality(convertTermToKernel(left), convertTermToKernel(right))
      }
    )
  }

  /**
   * @param term a tptp term in leo parser
   * @return the same term in LISA
   */
  def convertTermToKernel(term: CNF.Term): K.Term = term match {
    case CNF.AtomicTerm(f, args) => K.Term(K.ConstantFunctionLabel(f, args.size), args map convertTermToKernel)
    case CNF.Variable(name) => K.VariableTerm(K.VariableLabel(name))
    case CNF.DistinctObject(name) => ???
  }

  /**
   * @param term a tptp term in leo parser
   * @return the same term in LISA
   */
  def convertTermToKernel(term: FOF.Term): K.Term = term match {
    case FOF.AtomicTerm(f, args) =>
      K.Term(K.ConstantFunctionLabel(f, args.size), args map convertTermToKernel)
    case FOF.Variable(name) => K.VariableTerm(K.VariableLabel(name))
    case FOF.DistinctObject(name) => ???
    case FOF.NumberTerm(value) => ???
  }

  /**
   * @param formula an annotated tptp formula
   * @return the corresponding LISA formula augmented with name and role.
   */
  def annotatedFormulaToKernel(formula: String): AnnotatedFormula = {
    val i = Parser.annotatedFOF(formula)
    i.formula match {
      case FOF.Logical(formula) => AnnotatedFormula(i.role, i.name, convertToKernel(formula))
    }
  }

  private def problemToKernel(problemFile: File, md: ProblemMetadata): Problem = {
    val file = io.Source.fromFile(problemFile)
    val pattern = "SPC\\s*:\\s*[A-z]{3}(_[A-z]{3})*".r
    val g = file.getLines()

    def search(): String = pattern.findFirstIn(g.next()).getOrElse(search())

    val i = Parser.problem(file)
    val sq = i.formulas map {
      case TPTP.FOFAnnotated(name, role, formula, annotations) =>
        formula match {
          case FOF.Logical(formula) => AnnotatedFormula(role, name, convertToKernel(formula))
        }
      case TPTP.CNFAnnotated(name, role, formula, annotations) =>
        formula match {
          case CNF.Logical(formula) => AnnotatedFormula(role, name, convertToKernel(formula))
        }
      case _ => throw FileNotAcceptedException("Only FOF formulas are supported", problemFile.getPath)
    }
    Problem(md.file, md.domain, md.problem, md.status, md.spc, sq)
  }

  /**
   * @param problemFile a file containning a tptp problem
   * @return a Problem object containing the data of the tptp problem in LISA representation
   */
  def problemToKernel(problemFile: File): Problem = {
    problemToKernel(problemFile, getProblemInfos(problemFile))
  }

  /**
   * @param problemFile a path to a file containing a tptp problem
   * @return a Problem object containing the data of the tptp problem in LISA representation
   */
  def problemToKernel(problemFile: String): Problem = {
    problemToKernel(File(problemFile))
  }

  /**
   * Given a problem consisting of many axioms and a single conjecture, create a sequent with axioms on the left
   * and conjecture on the right.
   *
   * @param problem a problem, containing a list of annotated formulas from a tptp file
   * @return a sequent with axioms of the problem on the left, and the conjecture on the right
   */
  def problemToSequent(problem: Problem): LK.Sequent = {
    if (problem.spc.contains("CNF")) problem.formulas.map(_.formula) |- ()
    else
      problem.formulas.foldLeft[LK.Sequent](() |- ())((s, f) =>
        if (f._1 == "axiom") s +< f._3
        else if (f._1 == "conjecture" && s.right.isEmpty) s +> f._3
        else throw Exception("Can only agglomerate axioms and one conjecture into a sequents")
      )
  }

  /**
   * Given a folder containing folders containing problem (typical organisation of TPTP library) and a list of spc,
   * return the same arrangement of problems in LISA syntax, filtered so that only problems with at least one
   * spc from the "spc" argument.
   *
   * @param spc  a list of 3-characters codes representing properties of a problem, such as FOF for First Order Logic.
   * @param path the path to the tptp library.
   * @return A sequence of domains, each being a sequence of problems
   */
  def gatherAllTPTPFormulas(spc: Seq[String], path: String): Seq[Seq[Problem]] = {
    val d = new File(path)
    val probfiles: Array[File] = if (d.exists) {
      if (d.isDirectory) {
        if (d.listFiles().isEmpty) println("empty directory")
        d.listFiles.filter(_.isDirectory)

      } else throw new Exception("Specified path is not a directory.")
    } else throw new Exception("Specified path does not exist.")

    probfiles.map(d => gatherFormulas(spc, d.getPath)).toSeq
  }

  def gatherFormulas(spc: Seq[String], path: String): Seq[Problem] = {
    val d = new File(path)
    val probfiles: Array[File] = if (d.exists) {
      if (d.isDirectory) {
        if (d.listFiles().isEmpty) println("empty directory")
        d.listFiles.filter(_.isFile)

      } else throw new Exception("Specified path is not a directory.")
    } else throw new Exception("Specified path does not exist.")

    val r = probfiles.foldRight(List.empty[Problem])((p, current) => {
      val md = getProblemInfos(p)
      if (md.spc.exists(spc.contains)) problemToKernel(p, md) :: current
      else current
    })
    r
  }

  /**
   * @param file a file containing a tptp problem
   * @return the metadata info (file name, domain, problem, status and spc) in the file
   */
  private def getProblemInfos(file: File): ProblemMetadata = {
    val pattern = "((File)|(Domain)|(Problem)|(Status)|(SPC))\\s*:.*".r
    val s = io.Source.fromFile(file)
    val g = s.getLines()
    var fil: String = "?"
    var dom: String = "?"
    var pro: String = "?"
    var sta: String = "?"
    var spc: Seq[String] = Seq()

    val count: Int = 0
    while (g.hasNext && count < 5) {
      val line = g.next()
      val res = pattern.findFirstIn(line)
      if (res.nonEmpty) {
        val act = res.get
        if (act(0) == 'F') fil = act.drop(act.indexOf(":") + 2)
        else if (act(0) == 'D') dom = act.drop(act.indexOf(":") + 2)
        else if (act(0) == 'P') pro = act.drop(act.indexOf(":") + 2)
        else if (act(1) == 't') sta = act.drop(act.indexOf(":") + 2)
        else if (act(1) == 'P') spc = act.drop(act.indexOf(":") + 2).split("_").toIndexedSeq
      }
    }
    s.close()
    ProblemMetadata(fil, dom, pro, sta, spc)
  }

}
