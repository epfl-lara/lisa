
package lisa.hol
import lisa.maths.settheory.types.TypeSystem.*
import lisa.maths.settheory.types.TypeLib.*
import lisa.maths.settheory.SetTheory.{pair, ∅}

import lisa.fol.FOL as F
import lisa.fol.FOL.{Identifier, Term}


object VarsAndFunctions {


  

  class TypedForall( val v: F.Variable, val prop: F.Formula ) extends F.BinderFormula(F.forall, v, v match {
    case v: TypedVar => (v is v.typ) ==> prop
    case _ => prop
  }
  ) {
    override def toString = s"∀$v. $prop"
  }


  def tforall(v: TypedVar, prop: F.Formula): TypedForall = TypedForall(v, prop)

  var counter: Int = -1

  type VarTypeAssignment = F.Formula & TypeAssignment[Type] {val t:Variable}
  

  def nextId: Identifier = {
    counter += 1
    Identifier("$λ", counter)
  }

  type Type = Term

  class TypedVar( id: Identifier, val typ: Type ) extends F.Variable(id){
    override def toString = s"(${id.name}: $typ)"
  }
  
  def variable(using name: sourcecode.Name)(typ: Type): Variable = new TypedVar(Identifier(name.value), typ)

  def setTuple( vars: Seq[Term] ): Term = {
    vars.foldRight[Term](∅) { (acc, v) => 
      pair(v, acc)
    }
  }

  class AbstrVar( id: Identifier, val prop:Formula ) extends F.Variable(id){
    override def toString = s"(${id.name})"
  }

  class Abstraction(
    val bound: TypedVar,
    val body: Term,
    val repr: F.Variable,
    val freeVarsTuple: Term,
    val prop: F.Formula
  ) extends AppliedFunction(repr, freeVarsTuple) {

    override def toString = s"(λ$bound. $body)"
  }

  object Abstraction {
    def apply(bound: TypedVar, body: Term): Abstraction = {
      val repr = F.Variable(nextId)
      val freevars = (body.freeVariables - bound).toSeq.sortBy(_.id.name)
      val freeVarsTuple = setTuple(freevars)
      val inner = tforall(bound, app(app(repr, freeVarsTuple), bound) === body)
      val prop = freevars.foldRight[Formula](inner) { (v, acc) => 
        v match {
          case v: TypedVar => tforall(v, acc)
          case _ => F.forall(v, acc)
        }
      }
      val abstrRepr = new AbstrVar(nextId, prop)
      new Abstraction(bound, body, abstrRepr, freeVarsTuple, prop)
    }
  }





  private def HOLSeqToFOLSeq(left: Set[Term], right: Term): (Set[VarTypeAssignment], Set[Formula]) = {
    val frees = left.flatMap(_.freeVariables) ++ right.freeVariables
    val (r1, r2) = frees.foldLeft((List.empty[VarTypeAssignment], List.empty[Formula])) { 
      case ((acc1, acc2), v: TypedVar) => 
        ((v is v.typ).asInstanceOf[VarTypeAssignment] :: acc1, acc2)
      case ((acc1, acc2), a: AbstrVar) => 
        (acc1, a.prop :: acc2)
      case ((acc1, acc2), v) => 
        (acc1, acc2)
    }
    (r1.toSet, r2.toSet)
    
  }

  class HOLSequent(
    val premises: Set[Term],
    val conclusion: Term,
    varTypes: Set[VarTypeAssignment],
    abstrs: Set[Formula]
    ) extends F.Sequent(premises.map(_ === One) ++ varTypes ++ abstrs, Set(conclusion === One)) {
    
  }

  object HOLSequent {
    def apply(premises: Set[Term], conclusion: Term): HOLSequent = {
      val (valTypes, abstr) = HOLSeqToFOLSeq(premises, conclusion)
      new HOLSequent(premises, conclusion, valTypes, abstr)
    }
  }


  def TypingTheorem(using lisa.prooflib.OutputManager)(assignment: TypeAssignment[Type]): THM = 
    val (l1, l2) = HOLSeqToFOLSeq(Set.empty, assignment.t)
    Theorem(F.Sequent(l1 ++ l2, Set(assignment.t is assignment.typ))) {
      have(thesis) by TypeChecker.prove
    }
    
  





  // Sequent Syntax

  trait TernSetConverter[T] {
    def apply(t: T): Set[Term]
  }

  given TernSetConverter[Unit] with {
    override def apply(u: Unit): Set[Term] = Set.empty
  }

  given TernSetConverter[EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[Term] = Set.empty
  }

  given [H <: Term, T <: Tuple](using c: TernSetConverter[T]): TernSetConverter[H *: T] with {
    override def apply(t: H *: T): Set[Term] = c.apply(t.tail) + t.head
  }

  given term_to_set[T <: Term]: TernSetConverter[T] with {
    override def apply(f: T): Set[Term] = Set(f)
  }

  given iterable_to_set[T <: Term, I <: Iterable[T]]: TernSetConverter[I] with {
    override def apply(s: I): Set[Term] = s.toSet
  }

  private def any2set[A, T <: A](any: T)(using c: TernSetConverter[T]): Set[Term] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using TernSetConverter[T1]) {
    infix def |-(right: Term): HOLSequent = HOLSequent(any2set(left), right)
    infix def ⊢(right: Term): HOLSequent = HOLSequent(any2set(left), right)
  }

}
