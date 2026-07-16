package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base.Predef._

import PartialOrder._

/**
 * Given a partial order `(A, <)`, a set `S ⊆ A` is a lower set of `A` if
 * whenever `x ∈ S` and `y < x` then necessarily `y ∈ S`. `S` is also said to
 * be downward-closed.
 *
 * In the context of [[WellOrders]], `S ⊂ A` is downward-closed if and only if
 * it is of the form `S = {y ∈ A | y < x}` for some `x ∈ A`.
 */
object LowerSet extends lisa.Main {

  private val S = variable[Ind]

  /**
   * Definition --- `S ⊆ A` is downward-closed of `A` if `x ∈ S` and `y < x` implies
   * `y ∈ S`.
   */
  val lowerSet = DEF(λ(S, λ(A, λ(<, S ⊆ A /\ ∀(x ∈ S, ∀(y ∈ A, y < x ==> y ∈ S))))))

  /**
   * Theorem --- Quantifier-free reformulation of the definition.
   */
  val membership = Theorem(
    (lowerSet(S)(A)(<), x ∈ S, y ∈ A, y < x) |- y ∈ S
  ) {
    assume(lowerSet(S)(A)(<))
    have(∀(x ∈ S, ∀(y ∈ A, y < x ==> y ∈ S))) by Tautology.from(lowerSet.definition)
    thenHave(x ∈ S |- ∀(y ∈ A, y < x ==> y ∈ S)) by InstantiateForall(x)
    thenHave(thesis) by InstantiateForall(y)
  }

  /**
   * Theorem --- The empty set is (vacuously) a lower set of `(A, <)`.
   */
  val empty = Theorem(
    lowerSet(∅)(A)(<)
  ) {
    have(x ∈ ∅ ==> ∀(y ∈ A, y < x ==> y ∈ ∅)) by Tautology.from(EmptySet.definition)
    thenHave(∀(x ∈ ∅, ∀(y ∈ A, y < x ==> y ∈ ∅))) by RightForall
    thenHave(∅ ⊆ A /\ ∀(x ∈ ∅, ∀(y ∈ A, y < x ==> y ∈ ∅))) by Tautology.fromLastStep(Subset.leftEmpty of (x := A))
    thenHave(thesis) by Substitute(lowerSet.definition of (S := ∅))
  }

  /**
   * Theorem --- The union of lower sets is also a lower set.
   */
  val union = Theorem(
    ∀(X ∈ S, lowerSet(X)(A)(<)) |- lowerSet(⋃(S))(A)(<)
  ) {
    assume(∀(X ∈ S, lowerSet(X)(A)(<)))
    val `X ∈ S` = thenHave(X ∈ S |- lowerSet(X)(A)(<)) by InstantiateForall(X)

    thenHave(X ∈ S ==> X ⊆ A) by Tautology.fromLastStep(lowerSet.definition of (S := X))
    thenHave(∀(X ∈ S, X ⊆ A)) by RightForall
    val `⋃S ⊆ A` = thenHave(⋃(S) ⊆ A) by Tautology.fromLastStep(Union.leftUnaryUnionSubset of (x := S, z := A))

    have((X ∈ S, x ∈ X, y ∈ A, y < x) |- (X ∈ S) /\ (y ∈ X)) by Tautology.from(
      membership of (S := X),
      `X ∈ S`
    )
    thenHave((X ∈ S, x ∈ X, y ∈ A, y < x) |- ∃(X, (X ∈ S) /\ (y ∈ X))) by RightExists
    thenHave((X ∈ S, x ∈ X, y ∈ A, y < x) |- y ∈ ⋃(S)) by Substitute(
      ⋃.definition of (x := S, z := y)
    )
    thenHave((X ∈ S, x ∈ X) |- (y ∈ A) ==> ((y < x) ==> y ∈ ⋃(S))) by Restate
    thenHave((X ∈ S, x ∈ X) |- ∀(y ∈ A, (y < x) ==> y ∈ ⋃(S))) by RightForall
    thenHave((x ∈ X) /\ (X ∈ S) |- ∀(y ∈ A, (y < x) ==> y ∈ ⋃(S))) by Restate
    thenHave(∃(X, (x ∈ X) /\ (X ∈ S)) |- ∀(y ∈ A, (y < x) ==> y ∈ ⋃(S))) by LeftExists
    thenHave(x ∈ ⋃(S) ==> ∀(y ∈ A, (y < x) ==> y ∈ ⋃(S))) by Tautology.fromLastStep(
      ⋃.definition of (x := S, z := x)
    )
    thenHave(∀(x ∈ ⋃(S), ∀(y ∈ A, (y < x) ==> y ∈ ⋃(S)))) by RightForall
    thenHave(∀(x ∈ ⋃(S), ∀(y ∈ A, (y < x) ==> y ∈ ⋃(S)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      lowerSet.definition of (S := ⋃(S)),
      `⋃S ⊆ A`
    )
  }

}
