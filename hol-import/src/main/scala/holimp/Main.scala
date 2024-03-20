package holimp

import Core.*
import upickle.default.{ReadWriter => RW, *}
import Parser._
import upickle.default
import java.io.File

object JSONParser:
  case class SplitProofStep(name: String, dep1: Int, dep2: Int, strdep: String, termdep: String, termsdeps: List[List[String]], typesdeps: List[List[String]])

  case class RawStep(id: Int, pr: SplitProofStep)

  given rws: RW[SplitProofStep] = macroRW 
  given rw: RW[RawStep] = macroRW 

  val fileBase = "../proofs/prooftrace2"

  def readJSON(file: File) = 
    read[Array[RawStep]](file)

  case class UnknownProofStepException(name: String) extends Exception
  case class CouldNotParseException(msg: String, next: String) extends Exception(s"Could not parse\n\tMessage: $msg\n\tNext: $next")
  case object IncompleteParsingException extends Exception
  case object UnreachableCaseException extends Exception
  
  extension [T] (res: ParseResult[T])
    def getDone =
      res match
        case Success(out, next) if next.atEnd => out
        case Success(_, _) => throw IncompleteParsingException
        case NoSuccess(msg, next) => throw CouldNotParseException(msg, next.toString())
        case _ => throw UnreachableCaseException
      

  def parseTerm(str: String): Term = parse(term, str).getDone

  def parseAsVar(str: String): Variable = parse(variable, str).getDone

  def parseInst(insts: List[List[String]]): Map[Variable, Term] = 
    insts.map{ case List(left, right) => parseAsVar(left) -> parseTerm(right); case _ => throw UnreachableCaseException}.toMap

  def parseTypeInst(insts: List[List[String]]): Map[TypeVariable, Type] = 
    def parseAsTVar(str: String) = parse(typeVariable, str).getDone
    def parseType(str: String) = parse(typ, str).getDone
    insts.map{ case List(left, right) => parseAsTVar(left) -> parseType(right); case _ => throw UnreachableCaseException}.toMap


  val stepDict = Map.empty[Int, ProofStep]

  def processSplitStep(step: SplitProofStep, map: Map[Int, ProofStep]): ProofStep = 
    step.name match
      case "REFL" => REFL(parseTerm(step.termdep))
      case "TRANS" => TRANS(map(step.dep1), map(step.dep2))
      case "MK_COMB" => MK_COMB(map(step.dep1), map(step.dep2))
      case "ABS" => ABS(parseAsVar(step.termdep), map(step.dep1))
      case "BETA" => BETA(parseTerm(step.termdep))
      case "ASSUME" => ASSUME(parseTerm(step.termdep))
      case "EQ_MP" => EQ_MP(map(step.dep1), map(step.dep2))
      case "DEDUCT_ANTISYM_RULE" => DEDUCT_ANTISYM_RULE(map(step.dep1), map(step.dep2))
      case "INST" => INST(map(step.dep1), parseInst(step.termsdeps))
      case "INST_TYPE" => INST_TYPE(map(step.dep1), parseTypeInst(step.typesdeps))
      case "AXIOM" => AXIOM(parseTerm(step.termdep))
      case "DEFINITION" => DEFINITION(step.strdep, parseTerm(step.termdep))
      case "TYPE_DEFINITION" => TYPE_DEFINITION(step.strdep, parseTerm(step.termdep), map(step.dep1))
      case _ => throw UnknownProofStepException(step.name)


  def getProofs =
    val rawSteps = readJSON(File(s"$fileBase.proofs"))
    val mapped = rawSteps.foldLeft(Map.empty[Int, ProofStep]) { case (map, RawStep(i, step)) =>
      val readStep = processSplitStep(step, map)
      map + (i -> readStep)
    }
    mapped

  case class TheoremRef(id: Int, nm: String)

  def getTheorems =
    given rwt: RW[TheoremRef] = macroRW
    read[List[TheoremRef]](File(s"$fileBase.names"))

  def getStatements =
    case class Sequent(hy: List[String], cc: String)
    case class TheoremStatement(id: Int, th: Sequent)
    given rwns: RW[Sequent] = macroRW
    given rwn: RW[TheoremStatement] = macroRW
    read[Array[TheoremStatement]](File(s"$fileBase.theorems")).map(th => th.id -> (th.th.hy.map(parseTerm), parseTerm(th.th.cc))).toMap

@main def hello(): Unit =
  // val m = JSONParser.getProofs
  val thm = JSONParser.getStatements(188)
  println(thm._2.pretty)
