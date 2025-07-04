package lisa.maths.SetTheory.Order
package Examples

import lisa.maths.SetTheory.Relations.Examples.EmptyRelation
import Definitions.*

/** The empty order is the order on the empty set.
  */
object EmptyOrder extends lisa.Main {

  private val A = variable[Ind]
  private val < = variable[Ind]
  private val X = variable[Ind]

  /** Theorem --- The empty set is a partial order on the empty-set.
    */
  val emptyOrderStrictPartialOrder = Theorem(
    strictPartialOrder(∅)(∅)
  ) {
    have(thesis) by Tautology.from(
      strictPartialOrder.definition of (A := ∅, < := ∅),
      EmptyRelation.emptyRelation of (X := ∅),
      EmptyRelation.emptyRelationTransitive,
      EmptyRelation.emptyRelationIrreflexive
    )
  }

  /** Theorem --- The empty set is a total order on the empty-set.
    */
  val emptyOrderTotalOrder = Theorem(
    totalOrder(∅)(∅)
  ) {
    have(thesis) by Tautology.from(
      totalOrder.definition of (A := ∅, < := ∅),
      emptyOrderStrictPartialOrder,
      EmptyRelation.emptyRelationTotal
    )
  }

}
