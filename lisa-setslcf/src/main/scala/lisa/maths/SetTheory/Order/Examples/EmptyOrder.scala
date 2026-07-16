package lisa.maths.SetTheory.Order
package Examples

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Examples.EmptyRelation
import lisa.maths.SetTheory.Relations.Predef._

import PartialOrder._
import TotalOrder._

/**
 * The empty order is the order on the empty set.
 */
object EmptyOrder extends lisa.Main {

  /**
   * Theorem --- The empty set is a partial order on the empty-set.
   */
  val isStrictPartialOrder = Theorem(
    strictPartialOrder(∅)(∅)
  ) {
    have(thesis) by Tautology.from(
      strictPartialOrder.definition of (A := ∅, < := ∅),
      EmptyRelation.emptyRelation of (X := ∅),
      Relations.BasicTheorems.relationOnIsRelation of (R := ∅, X := ∅),
      EmptyRelation.emptyRelationTransitive of (X := ∅),
      EmptyRelation.emptyRelationIrreflexive of (X := ∅)
    )
  }

  /**
   * Theorem --- The empty set is a total order on the empty-set.
   */
  val isStrictTotalOrder = Theorem(
    strictTotalOrder(∅)(∅)
  ) {
    have(thesis) by Tautology.from(
      strictTotalOrder.definition of (A := ∅, < := ∅),
      isStrictPartialOrder,
      EmptyRelation.emptyRelationTotal
    )
  }

}
