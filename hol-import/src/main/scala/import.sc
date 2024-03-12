//> using dep "com.lihaoyi::upickle:3.2.0"

object Core:

  case class ApplicationOnNonFunctionException(term: Term) extends Exception(s"Constructed a term applying to a non-function.\n\tTerm: $term")

  sealed trait Type
  case object Unit extends Type
  case object Bool extends Type
  case object Ind extends Type
  case class Func(inputType: Type, outputType: Type) extends Type
  case class TypeVariable(name: String) extends Type
  case class CustomType(name:String) extends Type

  sealed trait Term:
    def tpe: Type
  case class Variable(name: String, tpe: Type) extends Term
  case class Abstraction(x: Variable, inner: Term) extends Term:
    def tpe: Type = Func(x.tpe, inner.tpe)
  case class Application(fun: Term, arg: Term) extends Term:
    def tpe: Type = 
      fun.tpe match
        case Func(inputType, outputType) => outputType
        case _ => throw ApplicationOnNonFunctionException(this)
  case class Constant(name: String, tpe: Type, paramTypes: List[TypeVariable]) extends Term
end Core

import Core.*

import upickle.default.*
import upickle.default.{ReadWriter => RW, macroRW}

case class SplitProofStep(name: String, dep1: Int, dep2: Int, strdep: String, termdep: String, termsdeps: List[List[String]], typesdeps: List[List[String]])

case class RawStep(id: Int, pr: SplitProofStep)

given rws: RW[SplitProofStep] = macroRW 
given rw: RW[RawStep] = macroRW 

sealed trait ProofStep
case class REFL(term: Term) extends ProofStep
case class TRANS(left: ProofStep, right: ProofStep) extends ProofStep
case class MK_COMB(left: ProofStep, right: ProofStep) extends ProofStep
case class ABS(absVar: Variable, from: ProofStep) extends ProofStep
case class BETA(from: ProofStep) extends ProofStep
case class ASSUME(term: Term) extends ProofStep
case class EQ_MP(left: ProofStep, right: ProofStep) extends ProofStep
case class DEDUCT_ANTISYM_RULE(left: ProofStep, right: ProofStep) extends ProofStep
case class INST(from: ProofStep, insts: Map[Variable, Term]) extends ProofStep
case class INST_TYPE(from: ProofStep, insts: Map[TypeVariable, Type]) extends ProofStep
case class AXIOM(term: Term) extends ProofStep
case class DEFINITION(name: String, term: Term) extends ProofStep
case class TYPE_DEFINITION(name: String, term: Term, just: ProofStep) extends ProofStep

case class UnknownProofStepException(name: String) extends Exception

def parseTerm(str: String): Term = 
  def rec(str: String): Option[Term] =
    val leading = str(0) 
    ???
  rec(str).get

def parseAsVar(str: String): Variable = ???

def parseInst(insts: List[List[String]]): Map[Variable, Term] = ???

def parseTypeInst(insts: List[List[String]]): Map[TypeVariable, Type] = ???

val stepDict = Map.empty[Int, ProofStep]

def processSplitStep(using map: Map[Int, ProofStep])(step: SplitProofStep): ProofStep = 
  step.name match
    case "REFL" => REFL(parseTerm(step.termdep))
    case "TRANS" => TRANS(map(step.dep1), map(step.dep2))
    case "MK_COMB" => MK_COMB(map(step.dep1), map(step.dep2))
    case "ABS" => ABS(parseAsVar(step.termdep), map(step.dep1))
    case "BETA" => BETA(map(step.dep1))
    case "ASSUME" => ASSUME(parseTerm(step.termdep))
    case "EQ_MP" => EQ_MP(map(step.dep1), map(step.dep2))
    case "DEDUCT_ANTISYM_RULE" => DEDUCT_ANTISYM_RULE(map(step.dep1), map(step.dep2))
    case "INST" => INST(map(step.dep1), parseInst(step.termsdeps))
    case "INST_TYPE" => INST_TYPE(map(step.dep1), parseTypeInst(step.typesdeps))
    case "AXIOM" => AXIOM(parseTerm(step.termdep))
    case "DEFINITION" => DEFINITION(step.strdep, parseTerm(step.termdep))
    case "TYPE_DEFINITION" => TYPE_DEFINITION(step.strdep, parseTerm(step.termdep), map(step.dep1))
    case _ => throw UnknownProofStepException(step.name)

val rawSteps = read[Array[RawStep]](java.io.File("new.proofs"))
val mapped = rawSteps.foldLeft(stepDict) { case (map, RawStep(i, step)) =>
  val readStep = processSplitStep(using map)(step)
  map + (i -> readStep)
}
println(mapped)

