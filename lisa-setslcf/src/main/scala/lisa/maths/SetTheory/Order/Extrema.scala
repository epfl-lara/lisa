package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base.Predef._

import PartialOrder._

/**
 * This file defines extremal elements of an order:
 * - Maximal and minimal elements
 * - Upper and lower bounds
 * - Greatest and least elements
 *
 * TODO: Define the LUB and GLB (maybe in a separate file).
 */
object Extrema extends lisa.Main {

  /**
   * Maximal element --- `a ∈ A` is a maximal element of `A` with respect to `<` if
   *
   *    `∀ x ∈ A. ¬(a < x)`
   */
  val maximal = DEF(λ(a, λ(A, λ(<, a ∈ A /\ ∀(x, x ∈ A ==> ¬(a < x))))))

  /**
   * Minimal element --- `a ∈ A` is a minimal element of `A` with respect to `<` if
   *
   *    `∀ x ∈ A. ¬(x < a)`
   */
  val minimal = DEF(λ(a, λ(A, λ(<, a ∈ A /\ ∀(x, x ∈ A ==> ¬(x < a))))))

  /**
   * Upper bound --- `a` is an upper bound of `A` with respect to `<` if
   *
   *    `∀ x ∈ A. x <= a`
   *
   * Note that `a ∈ A` is not required.
   */
  val upperBound = DEF(λ(a, λ(A, λ(<, ∀(x, x ∈ A ==> (x < a) \/ (x === a))))))

  /**
   * Lower bound --- `a` is a lower bound on `A` with respect to `<` if
   *
   *    `∀ x ∈ A. a <= x`
   *
   * Note that `a ∈ A` is not required.
   */
  val lowerBound = DEF(λ(a, λ(A, λ(<, ∀(x, x ∈ A ==> (a < x) \/ (x === a))))))

  /**
   * Greatest element --- `a ∈ A` is the greatest element of `A` with respect to `<` if
   *
   *    `∀ x ∈ A. x <= a`
   *
   * In other words, `a` is an upper bound on `A` such that `a ∈ A`.
   */
  val greatest = DEF(λ(a, λ(A, λ(<, (a ∈ A) /\ upperBound(a)(A)(<)))))

  /**
   * Least element --- `a ∈ A` is the least element of `A` with respect to `<` if
   *
   *    `∀ x ∈ A. a <= x`
   *
   * In other words, `a` is a lower bound on `A` such that `a ∈ A`.
   */
  val least = DEF(λ(a, λ(A, λ(<, (a ∈ A) /\ lowerBound(a)(A)(<)))))

}
