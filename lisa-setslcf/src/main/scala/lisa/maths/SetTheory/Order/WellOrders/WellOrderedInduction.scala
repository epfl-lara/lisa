package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Relations.Predef._

import PartialOrder._
import WellOrder._

/**
 * Given a well-ordered set `(A, <)`, one can that a property `P` holds on `A`
 * by proving that `P(x)` holds for any `x ∈ A`, assuming that `P(y)` holds for
 * all `y < x`.
 *
 * This is essentially the [[WellFoundedRelation.induction]] for total orders.
 */
object WellOrderedInduction extends lisa.Main {

  private val X = variable[Ind]
  private val R = variable[Ind]

  /**
   * Well-ordered induction --- If `P(x)` holds for any `x ∈ A` assuming that
   * `P(y)` holds for all `y < x`, then `P(x)` holds for all `x ∈ A`.
   *
   * Essentially [[WellFoundedRelation.induction]] specialized to total orders.
   */
  val induction = Theorem(
    (
      wellOrder(A)(<),
      ∀(x ∈ A, ∀(y ∈ A, y < x ==> P(y)) ==> P(x))
    ) |-
      ∀(x ∈ A, P(x))
  ) {
    have(thesis) by Tautology.from(
      wellOrder.definition,
      WellFoundedRelation.induction of (R := <, X := A)
    )
  }
}
