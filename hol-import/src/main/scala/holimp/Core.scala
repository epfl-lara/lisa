package holimp

import java.awt.Window.Type

object Core:

  case class ApplicationOnNonFunctionException(term: Term) extends Exception(s"Constructed a term applying to a non-function.\n\tTerm: $term")

  sealed trait Type
  case class TypeVariable(name: String) extends Type
  case class TypeApplication(name: String, args: List[Type]) extends Type

  val BoolType = TypeApplication("bool", Nil)

  object FunType:
    def apply(in: Type, out: Type): Type = 
      TypeApplication("fun", List(in, out))
    def unapply(t: Type): Option[(Type, Type)] =
      t match
        case TypeApplication("fun", List(in, out)) => Some((in, out))
        case  _ => None

  sealed trait Term:
    def tpe: Type

  case class Variable(name: String, tpe: Type) extends Term
  case class Constant(name: String, tpe: Type) extends Term
  case class Combination(left: Term, right: Term) extends Term:
    def tpe: Type = 
      left.tpe match
        case FunType(_, out) => out
        case _ => throw ApplicationOnNonFunctionException(this)

  case class Abstraction(absVar: Variable, inner: Term) extends Term:
    def tpe: Type = 
      FunType(absVar.tpe, inner.tpe)

  sealed trait ProofStep
  case class REFL(term: Term) extends ProofStep
  case class TRANS(left: ProofStep, right: ProofStep) extends ProofStep
  case class MK_COMB(left: ProofStep, right: ProofStep) extends ProofStep
  case class ABS(absVar: Variable, from: ProofStep) extends ProofStep
  case class BETA(term: Term) extends ProofStep
  case class ASSUME(term: Term) extends ProofStep
  case class EQ_MP(left: ProofStep, right: ProofStep) extends ProofStep
  case class DEDUCT_ANTISYM_RULE(left: ProofStep, right: ProofStep) extends ProofStep
  case class INST(from: ProofStep, insts: Map[Variable, Term]) extends ProofStep
  case class INST_TYPE(from: ProofStep, insts: Map[TypeVariable, Type]) extends ProofStep
  case class AXIOM(term: Term) extends ProofStep
  case class DEFINITION(name: String, term: Term) extends ProofStep
  case class TYPE_DEFINITION(name: String, term: Term, just: ProofStep) extends ProofStep

  extension (t : Type) def pretty: String =
    t match
      case BoolType => "B"
      case FunType(from, to) => s"(${from.pretty} => ${to.pretty})"
      case TypeVariable(name) => name
      case TypeApplication(name, args) => s"$name[${args.mkString(", ")}]"

  extension (t: Term) def pretty: String =
    t match
      case Variable(name, tpe) => s"$name : ${tpe.pretty}"
      case Constant(name, tpe) => s"$name : ${tpe.pretty}"
      case Combination(left, right) => s"(${left.pretty}) (${right.pretty})"
      case Abstraction(absVar, inner) => s"\\${absVar.pretty}. ${inner.pretty}"    

end Core
