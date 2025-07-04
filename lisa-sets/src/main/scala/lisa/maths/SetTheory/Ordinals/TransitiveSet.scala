package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Base.Predef.*
import lisa.maths.SetTheory.Relations.Predef.*
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation.*

/**
 * A transitive set `A` is a set such that elements of elements of `A` are also in `A`:
 * if `x ∈ A` and `y ∈ x`, then `y ∈ A`. This can also be restated as `x ∈ A ==> x ⊆ A`.
 *
 * Note that this is not the same as saying that the [[membershipRelation]] on
 * `A` is transitive, since for `x ∈ y ∈ z ∈ A` we do not necessarily have `x ∈ z`.
 */
object TransitiveSet extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val A = variable[Ind]

  /**
   * Definition --- `A` is transitive if `x ∈ y` and `y ∈ A` implies `x ∈ A`.
   *
   *   `transitiveSet(A) <=> ∀x, y. x ∈ y /\ y ∈ A ==> x ∈ A`
   */
  val transitiveSet = DEF(λ(A, ∀(x, ∀(y, x ∈ y /\ (y ∈ A) ==> x ∈ A))))

  /**
   * Theorem --- `A` is transitive if and only if `x ∈ A` implies `x ⊆ A`.
   *
   *   `transitiveSet(x) <=> ∀x. x ∈ A ==> x ⊆ A`
   */
  val alternativeDefinition = Theorem(
    transitiveSet(A) <=> ∀(x, x ∈ A ==> x ⊆ A)
  ) {
    val `==>` = have(transitiveSet(A) |- ∀(x, x ∈ A ==> x ⊆ A)) subproof {
      assume(transitiveSet(A))
      thenHave(∀(x, ∀(y, x ∈ y /\ (y ∈ A) ==> x ∈ A))) by Substitute(transitiveSet.definition)
      thenHave(y ∈ x /\ (x ∈ A) ==> y ∈ A) by InstantiateForall(y, x)
      thenHave(x ∈ A |- (y ∈ x) ==> (y ∈ A)) by Restate
      thenHave(x ∈ A |- ∀(y, (y ∈ x) ==> (y ∈ A))) by RightForall
      thenHave(x ∈ A |- x ⊆ A) by Substitute(⊆.definition)
      thenHave(x ∈ A ==> x ⊆ A) by Restate
      thenHave(thesis) by RightForall
    }

    val `<==` = have(∀(x, x ∈ A ==> x ⊆ A) |- transitiveSet(A)) subproof {
      assume(∀(x, x ∈ A ==> x ⊆ A))
      thenHave(y ∈ A ==> y ⊆ A) by InstantiateForall(y)
      thenHave(y ∈ A ==> ∀(x, x ∈ y ==> x ∈ A)) by Substitute(⊆.definition)
      thenHave(y ∈ A |- ∀(x, x ∈ y ==> x ∈ A)) by Restate
      thenHave(y ∈ A |- x ∈ y ==> x ∈ A) by InstantiateForall(x)
      thenHave(x ∈ y /\ (y ∈ A) ==> x ∈ A) by Restate
      thenHave(∀(x, ∀(y, x ∈ y /\ (y ∈ A) ==> x ∈ A))) by Generalize
      thenHave(thesis) by Substitute(transitiveSet.definition)
    }

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Theorem --- A transitive set `A` is indeed transitive.
   *
   *   `transitiveSet(A), x ∈ y, y ∈ A |- x ∈ A`
   *
   * Reformulation of the definition.
   */
  val transitivity = Theorem(
    (transitiveSet(A), x ∈ y, y ∈ A) |- x ∈ A
  ) {
    assume(transitiveSet(A))
    thenHave(∀(x, ∀(y, x ∈ y /\ (y ∈ A) ==> x ∈ A))) by Substitute(transitiveSet.definition)
    thenHave(x ∈ y /\ (y ∈ A) ==> x ∈ A) by InstantiateForall(x, y)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- The empty set is transitive.
   */
  val emptySet = Theorem(
    transitiveSet(∅)
  ) {
    have(x ∈ ∅ ==> x ⊆ ∅) by Tautology.from(EmptySet.definition)
    thenHave(∀(x, x ∈ ∅ ==> x ⊆ ∅)) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(alternativeDefinition of (A := ∅))
  }

}
