package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Relations.Predef._

import PartialOrder._

/**
 * A [[partialOrder]] `(A, <=)` is said to be total if `<=` is [[stronglyConnected]].
 * Similarly, a [[strictPartialOrder]] is total if `<` is [[connected]].
 *
 * Total orders are also called *linear orders*, since their elements can be placed in
 * a line such that `x < y` iff `x` comes before `y` in the line. In other words, their
 * Hasse diagram is a line.
 */
object TotalOrder extends lisa.Main {

  /**
   * Total order --- `(A, <=)` is a total order if `(A, <=)` is a
   * [[partialOrder]] and `<=` is [[stronglyConnected]].
   */
  val totalOrder = DEF(λ(A, λ(<, partialOrder(A)(<) /\ stronglyConnected(<)(A))))

  /**
   * Strict total order --- `(A, <)` is a strict total order if `(A, <)` is a
   * [[strictPartialOrder]] and `<` is [[total]].
   */
  val strictTotalOrder = DEF(λ(A, λ(<, strictPartialOrder(A)(<) /\ total(<)(A))))
}
