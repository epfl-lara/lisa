package lisa.maths.MathlibPort.Order

import lisa.maths.SetTheory.Order.{PartialOrder, TotalOrder}
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Order/Basic`.
 *
 * This file provides a small compatibility layer over the existing set-theoretic
 * order theory in `lisa.maths.SetTheory.Order.*`.
 */
object Basic extends lisa.Main {

  val A = variable[Ind]
  val le = variable[Ind]

  extension (x: Expr[Ind]) {
    infix def ≤(y: Expr[Ind]): Expr[Prop] = (x, y) ∈ le
  }

  /**
   * Preorder --- `(A, ≤)` is a preorder if `≤` is a binary relation that is
   * reflexive and transitive on `A`.
   */
  val preorder = DEF(λ(A, λ(le, relation(le) /\ transitive(le)(A) /\ reflexive(le)(A))))

  /**
   * Partial order --- re-export of set-theoretic definition (order-theoretic `≤`).
   *
   * Note: this corresponds to Lean's `PartialOrder` structure (up to encoding).
   */
  val partialOrder = PartialOrder.partialOrder

  /**
   * Linear/total order --- re-export of set-theoretic total order definition.
   *
   * Note: this corresponds to Lean's `LinearOrder` structure (up to encoding).
   */
  val linearOrder = TotalOrder.totalOrder

  val partialOrderImpliesPreorder = Theorem(
    partialOrder(A)(le) |- preorder(A)(le)
  ) {
    have(thesis) by Tautology.from(
      preorder.definition,
      PartialOrder.partialOrder.definition
    )
  }

  val linearOrderImpliesPartialOrder = Theorem(
    linearOrder(A)(le) |- partialOrder(A)(le)
  ) {
    have(thesis) by Tautology.from(
      TotalOrder.totalOrder.definition,
      PartialOrder.partialOrder.definition
    )
  }

  val linearOrderImpliesPreorder = Theorem(
    linearOrder(A)(le) |- preorder(A)(le)
  ) {
    have(thesis) by Tautology.from(
      linearOrderImpliesPartialOrder,
      partialOrderImpliesPreorder
    )
  }
}
