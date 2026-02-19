package holimp
package core

case class ApplicationOnNonFunctionException(term: Term) extends Exception(s"Constructed a term applying to a non-function.\n\tTerm: $term")


/**
  * The core simple types of HOL Light
  */
sealed trait Type
case class TypeVariable(name: String) extends Type
case class TypeApplication(name: String, args: List[Type]) extends Type

/**
  * The boolean type
  * 
  * Defined separately to special case printing
  */
val BoolType = TypeApplication("bool", Nil)

object FunType:
  def apply(in: Type, out: Type): Type = 
    TypeApplication("fun", List(in, out))

  def unapply(t: Type): Option[(Type, Type)] =
    t match
      case TypeApplication("fun", List(in, out)) => Some((in, out))
      case  _ => None

/**
  * The core simple typed terms of HOL Light
  */
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

/**
  * An HOL sequent `Γ |- t`
  * 
  * @param hyps the list of hypotheses (Γ)
  * @param concl the conclusion (t)
  */
case class HOLSequent(hyps: List[Term], concl: Term)

/**
  * HOL proof steps as defined by the HOL Light kernel.
  *
  * Any recursive steps store only the indices of their predcessors, since
  * during the import, we know these to be uniquely assigned. 
  */
sealed trait ProofStep
/**
  * --------------
  *    |- t = t
  * 
  * @param term term for reflexive equality
  */
case class REFL(term: Term) extends ProofStep
/**
  *  Γ |- t1 = t2   Π |- t2 = t3
  * -----------------------------
  *      Γ, Π |- t1 = t3
  *
  * @param left proof of Γ |- t1 = t2
  * @param right proof of Π |- t2 = t3
  */
case class TRANS(left: Long, right: Long) extends ProofStep
/**
  *  Γ |- f = g   Π |- x = y
  * -------------------------
  *    Γ, Π |- f x = g y
  *
  * @param left proof of Γ |- f = g
  * @param right proof of Π |- x = y
  */
case class MK_COMB(left: Long, right: Long) extends ProofStep
/**
  *      Γ |- t1 = t2
  * ----------------------
  *  Γ |- λx. t1 = λx. t2
  *
  * @param absVar variable to abstract over
  * @param from proof of Γ |- t1 = t2 (where x is not free in Γ)
  */
case class ABS(absVar: Variable, from: Long) extends ProofStep
/**
  * --------------------------
  *  |- (λx. t) x = t
  *
  * @param term the beta-redex term (λx. t) x
  */
case class BETA(term: Term) extends ProofStep
/**
  * -------------
  *  {p} |- p
  *
  * @param term boolean term p to assume
  */
case class ASSUME(term: Term) extends ProofStep
/**
  *  Γ |- p = q   Π |- p
  * ---------------------
  *      Γ, Π |- q
  *
  * @param left proof of Γ |- p = q
  * @param right proof of Π |- p
  */
case class EQ_MP(left: Long, right: Long) extends ProofStep
/**
  *    Γ |- p   Π |- q
  * -----------------------
  *  Γ - {q}, Π - {p} |- p = q
  *
  * @param left proof of Γ |- p
  * @param right proof of Π |- q
  */
case class DEDUCT_ANTISYM_RULE(left: Long, right: Long) extends ProofStep
/**
  *                   Γ |- p
  * -----------------------------------------
  *  Γ[t1/x1,...,tn/xn] |- p[t1/x1,...,tn/xn]
  *
  * @param from proof of Γ |- p
  * @param insts mapping from variables to their instantiating terms
  */
case class INST(from: Long, insts: Map[Variable, Term]) extends ProofStep
/**
  *                   Γ |- p
  * -----------------------------------------
  *  Γ[τ1/α1,...,τn/αn] |- p[τ1/α1,...,τn/αn]
  *
  * @param from proof of Γ |- p
  * @param insts mapping from type variables to their instantiating types
  */
case class INST_TYPE(from: Long, insts: Map[TypeVariable, Type]) extends ProofStep
/**
  * -----------
  *   |- axiom
  *
  * @param term the axiom term
  */
case class AXIOM(term: Term) extends ProofStep
/**
  * ----------------------
  *   |- name = term
  *
  * @param name the constant being defined
  * @param term the defining term
  */
case class DEFINITION(name: String, term: Term) extends ProofStep
/**
  *            |- ∃x. P x
  * ----------------------------------------
  *   |- (mk o dest) x = x, |- P (dest x)
  *
  * @param name the name of the new type
  * @param term the characteristic predicate P
  * @param just proof of |- ∃x. P x (non-emptiness witness)
  */
case class TYPE_DEFINITION(name: String, term: Term, just: Long) extends ProofStep

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
