package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef.*

/**
  * A partial order `(A, <=)` is a binary relation that is [[transitive]],
  * [[reflexive]] and [[antisymmetric]]. A strict partial order `(A, <)` is
  * [[transitive]] and [[irreflexive]].
  */
object PartialOrder extends lisa.Main {

  /** Order symbols. */
  val <, <= = variable[Ind]

  extension (x: Expr[Ind]) {
    private[Order] infix def <(y: Expr[Ind]): Expr[Prop] = (x, y) ∈ PartialOrder.<
    private[Order] infix def <=(y: Expr[Ind]): Expr[Prop] = (x, y) ∈ PartialOrder.<=
  }

  /**
   * Partial order --- `(A, <=)` is a partial order if `<=` is a
   * binary relation that is [[transitive]], [[reflexive]] and [[antisymmetric]].
   */
  val partialOrder = DEF(λ(A, λ(<=, relation(<=) /\ transitive(<=)(A) /\ reflexive(<=)(A) /\ antisymmetric(<=)(A))))


  /**
   * Strict partial order --- `(A, <)` is a strict partial order if `<` is a
   * binary relation that is [[transitive]] and [[irreflexive]].
   */
  val strictPartialOrder = DEF(λ(A, λ(<, relation(<) /\ transitive(<)(A) /\ irreflexive(<)(A))))


  /**
   * Theorem --- If `(A, <)` is a strict partial order, then `<` is antisymmetric.
   *
   * This follows from irreflexivity and the fact that `¬(x < y /\ y < x)`.
   */
  val strictPartialOrderAntisymmetric = Theorem(
    strictPartialOrder(A)(<) |- antisymmetric(<)(A)
  ) {
    assume(strictPartialOrder(A)(<))

    have(∀(x ∈ A, ¬(x < x))) by Tautology.from(
      strictPartialOrder.definition, irreflexive.definition of (R := <, X := A)
    )
    val irreflexivity = thenHave(x ∈ A ==> ¬(x < x)) by InstantiateForall(x)

    have(∀(x ∈ A, ∀(y ∈ A, ∀(z ∈ A, (x < y) /\ (y < z) ==> (x < z))))) by Tautology.from(strictPartialOrder.definition, transitive.definition of (R := <, X := A))
    thenHave(x ∈ A |- ∀(y ∈ A, ∀(z ∈ A, (x < y) /\ (y < z) ==> (x < z)))) by InstantiateForall(x)
    thenHave((x ∈ A, y ∈ A) |- ∀(z ∈ A, (x < y) /\ (y < z) ==> (x < z))) by InstantiateForall(y)
    thenHave((x ∈ A, y ∈ A) |- (x < y) /\ (y < x) ==> (x < x)) by InstantiateForall(x)
    thenHave((x ∈ A) |- y ∈ A ==> ((x < y) /\ (y < x) ==> (x === y))) by Tautology.fromLastStep(irreflexivity)
    thenHave(x ∈ A |- ∀(y ∈ A, (x < y) /\ (y < x) ==> (x === y))) by RightForall
    thenHave(x ∈ A ==> ∀(y ∈ A, (x < y) /\ (y < x) ==> (x === y))) by RightImplies
    thenHave(∀(x ∈ A, ∀(y ∈ A, (x < y) /\ (y < x) ==> (x === y)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      antisymmetric.definition of (R := <, X := A),
      strictPartialOrder.definition,
      Relations.BasicTheorems.relationOnIsRelation of (R := <, X := A)
    )
  }
}

