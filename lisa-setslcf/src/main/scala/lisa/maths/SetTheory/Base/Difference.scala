package lisa.maths.SetTheory.Base

import Comprehension.|
import Symbols._

/**
 * The difference of two sets `x` and `y` is the set `x ∖ y = {z ∈ x | z ∉ y}`.
 */
object Difference extends lisa.Main {

  /**
   * Set Difference --- Given two sets, produces the set that contains
   * elements in the first but not in the second.
   *
   *    `x ∖ y = {z ∈ x | z ∉ y}`
   *
   * @param x set
   * @param y set
   */
  val ∖ = DEF(λ(x, λ(y, { z ∈ x | z ∉ y }))).printInfix()
  val diff = ∖

  extension (x: Expr[Ind]) {
    infix def ∖(y: Expr[Ind]): Expr[Ind] = diff(x)(y)
  }
}
