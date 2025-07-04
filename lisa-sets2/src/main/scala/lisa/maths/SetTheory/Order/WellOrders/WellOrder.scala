package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Order.Examples.EmptyOrder

import Definitions.*

/** A well-ordering `(A, <)` is a partial order `<` on `A` such that every non-empty set
  * has a `<`-minimal element.
  *
  * Well-orders enable proofs by induction and constructions of functions by
  * recursion, using for any `x` the values of the set for all smaller `y`.
  *
  * Well-order are crucial in the theory of [[lisa.maths.SetTheory.Ordinals.Ordinal]],
  * since an [[Ordinal.ordinal]] is a [[TransitiveSet]] well-ordered by the
  * [[lisa.maths.SetTheory.Relations.Examples.MembershipRelation]].
  */
object WellOrder extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val A, B = variable[Ind]
  private val f = variable[Ind]
  private val < = variable[Ind]
  private val ℛ = variable[Ind]

  /** Well ordering --- We say that `<` well-orders `A` (or `(A, <)` is a
    * well-ordering) if `(A, <)` is a [[totalOrder]] such that every non-empty set
    * has a `<`-minimal element:
    *
    *   `wellOrdering(A, <) <=> totalOrder(A, <) /\ ∀B ⊆ A. B ≠ ∅ ==> ∃ x ∈ B. ∀ y ∈ B. ¬(y < x)`
    *
    * @see [[totalOrder]]
    */
  val wellOrdering = DEF(λ(A, λ(<, totalOrder(A)(<) /\ ∀(B, (B ⊆ A) /\ (B ≠ ∅) ==> ∃(x, x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ <))))))

  /** Empty well-ordering --- The empty set well-orders the empty set.
    */
  val emptySet = Theorem(
    wellOrdering(∅)(∅)
  ) {
    have((B ⊆ ∅) /\ (B ≠ ∅) ==> ∃(x, x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ ∅))) by Tautology.from(
      Subset.rightEmpty of (x := B)
    )
    thenHave(∀(B, (B ⊆ ∅) /\ (B ≠ ∅) ==> ∃(x, x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ ∅)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      EmptyOrder.emptyOrderTotalOrder,
      wellOrdering.definition of (A := ∅, < := ∅)
    )
  }

  /** Transitivity --- If `(A, <)` is a well-ordering then `<` is transitive.
    */
  val transitivity = Theorem(
    wellOrdering(A)(<) |- transitive(<)
  ) {
    have(thesis) by Tautology.from(
      wellOrdering.definition,
      totalOrder.definition,
      strictPartialOrder.definition
    )
  }

  /** Totality --- If `(A, <)` is a well-ordering then `<` is total on `A`.
    */
  val totality = Theorem(
    wellOrdering(A)(<) |- total(<)(A)
  ) {
    have(thesis) by Tautology.from(
      wellOrdering.definition,
      totalOrder.definition
    )
  }

  /** Theorem --- If `(A, <)` is a well-ordering, then for any non-empty `B ⊆ A`
    * there exists `x ∈ B` that is `<`-minimal.
    *
    * Reformulates the well-ordering principle.
    */
  val minimalElement = Theorem(
    (wellOrdering(A)(<), B ⊆ A, B ≠ ∅) |- ∃(x, x ∈ B /\ minimal(x)(B)(<))
  ) {
    assume(wellOrdering(A)(<))
    have(∀(B, (B ⊆ A) /\ (B ≠ ∅) ==> ∃(x, x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ <)))) by Tautology.from(wellOrdering.definition)
    thenHave((B ⊆ A) /\ (B ≠ ∅) ==> ∃(x, x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ <))) by InstantiateForall(B)
    val minimalElementExistence = thenHave((B ⊆ A, B ≠ ∅) |- ∃(x, x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ <))) by Restate

    have(x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ <) |- x ∈ B /\ minimal(x)(B)(<)) by Congruence.from(minimal.definition of (ℛ := <, A := B))
    thenHave(x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ <) |- ∃(x, x ∈ B /\ minimal(x)(B)(<))) by RightExists
    thenHave(∃(x, x ∈ B /\ ∀(y, y ∈ B ==> (y, x) ∉ <)) |- ∃(x, x ∈ B /\ minimal(x)(B)(<))) by LeftExists

    have(thesis) by Cut(minimalElementExistence, lastStep)
  }
}
