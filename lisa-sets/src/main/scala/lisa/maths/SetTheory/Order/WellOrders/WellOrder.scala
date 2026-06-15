package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Order.Examples.EmptyOrder

import Predef._

/**
 * A well-order `(A, <)` is a partial order `<` on `A` such that every non-empty set
 * has a `<`-minimal element.
 *
 * Well-orders enable proofs by induction and constructions of functions by
 * recursion, using for any `x` the values of the set for all smaller `y`.
 *
 * Well-orders are crucial in the theory of [[lisa.maths.SetTheory.Ordinals.Ordinal]],
 * since an [[Ordinal.ordinal]] is a [[TransitiveSet]] well-ordered by the
 * [[lisa.maths.SetTheory.Relations.Examples.MembershipRelation]].
 */
object WellOrder extends lisa.Main {

  private val X = variable[Ind]
  private val < = variable[Ind]
  private val R = variable[Ind]

  /**
   * Well-order --- We say that `<` well-orders `A` (or `(A, <)` is a
   * well-order) if `(A, <)` is a [[strictTotalOrder]] such that every
   * non-empty set has a `<`-minimal element:
   *
   *   `wellOrder(A, <) <=> strictTotalOrder(A, <) /\ ∀B ⊆ A. B ≠ ∅ ==> ∃ x ∈ B. ∀ y ∈ B. ¬(y < x)`
   *
   * In other words, `<` is well-founded on `A`.
   *
   * @see [[strictTotalOrder]]
   */
  val wellOrder = DEF(λ(A, λ(<, strictTotalOrder(A)(<) /\ wellFounded(<)(A))))

  /**
   * Empty well-order --- The empty set well-orders the empty set.
   */
  val emptySet = Theorem(
    wellOrder(∅)(∅)
  ) {
    have((B ⊆ ∅) /\ (B ≠ ∅) ==> ∃(x, x ∈ B /\ minimal(x)(B)(∅))) by Tautology.from(
      Subset.rightEmpty of (x := B)
    )
    thenHave(∀(B, (B ⊆ ∅) /\ (B ≠ ∅) ==> ∃(x, x ∈ B /\ minimal(x)(B)(∅)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      EmptyOrder.isStrictTotalOrder,
      wellOrder.definition of (A := ∅, < := ∅),
      wellFounded.definition of (R := ∅, X := ∅)
    )
  }

  /**
   * Transitivity --- If `(A, <)` is a well-order then `<` is transitive.
   */
  val transitivity = Theorem(
    wellOrder(A)(<) |- transitive(<)(A)
  ) {
    have(thesis) by Tautology.from(
      wellOrder.definition,
      strictTotalOrder.definition,
      strictPartialOrder.definition
    )
  }

  /**
   * Totality --- If `(A, <)` is a well-order then `<` is total on `A`.
   */
  val totality = Theorem(
    wellOrder(A)(<) |- total(<)(A)
  ) {
    have(thesis) by Tautology.from(
      wellOrder.definition,
      strictTotalOrder.definition
    )
  }

  /**
   * Irreflexivity --- If `(A, <)` is a well-order then `<` is irreflexive on `A`.
   */
  val irreflexivity = Theorem(
    wellOrder(A)(<) |- irreflexive(<)(A)
  ) {
    have(thesis) by Tautology.from(
      wellOrder.definition,
      strictTotalOrder.definition,
      strictPartialOrder.definition
    )
  }

  /**
   * Theorem --- If `(A, <)` is a well-order, then for any non-empty `B ⊆ A`
   * there exists `x ∈ B` that is `<`-minimal.
   *
   * Reformulates the well-foundedness.
   */
  val minimalElement = Theorem(
    (wellOrder(A)(<), B ⊆ A, B ≠ ∅) |- ∃(x, minimal(x)(B)(<))
  ) {
    assume(wellOrder(A)(<))
    have(∀(B, (B ⊆ A) /\ (B ≠ ∅) ==> ∃(x, minimal(x)(B)(<)))) by Tautology.from(
      wellOrder.definition,
      wellFounded.definition of (R := <, X := A)
    )
    thenHave(thesis) by InstantiateForall(B)
  }
}
