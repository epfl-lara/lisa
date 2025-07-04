package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.*

import lisa.maths.Quantifiers.Generalize

/**
 * This file defines:
 * - (Strict) partial and total orders
 * - Maximal, minimal elements
 * - Upper and lower bounds
 */
object Definitions extends lisa.Main {

  private val x, y = variable[Ind]
  private val A = variable[Ind]
  private val <, <= = variable[Ind]

  /**
   * Local notations for partial orders.
   */
  extension (x: set) {
    private infix def <(y: set): Expr[Prop] = (x, y) ∈ Definitions.<
    private infix def <=(y: set): Expr[Prop] = (x, y) ∈ Definitions.<=
  }

  /**
   * Partial order --- `(A, <=)` is a partial order if `<=` is a
   * binary relation that is [[transitive]], [[reflexive]] and [[antisymmetric]].
   */
  val partialOrder = DEF(λ(A, λ(<=, relationOn(<=)(A) /\ transitive(<=) /\ reflexive(<=)(A) /\ antisymmetric(<=))))

  /**
   * Strict partial order --- `(A, <)` is a strict partial order if `<` is a
   * binary relation that is [[transitive]] and [[irreflexive]].
   */
  val strictPartialOrder = DEF(λ(A, λ(<, relationOn(<)(A) /\ transitive(<) /\ irreflexive(<))))

  /**
   * Total order --- `(A, <)` is a total order if `(A, <)` is a
   * [[strictPartialOrder]] and `<` is [[total]].
   */
  val totalOrder = DEF(λ(A, λ(<, strictPartialOrder(A)(<) /\ total(<)(A))))

  /**
   * Maximal element --- `x` is a maximal element on `A` with respect to `<` if
   *
   *    `∀ y ∈ A. ¬(x < y)`
   */
  val maximal = DEF(λ(x, λ(A, λ(<, ∀(y, y ∈ A ==> ¬(x < y))))))

  /**
   * Minimal element --- `x` is a minimal element on `A` with respect to `<` if
   *
   *    `∀ y ∈ A. ¬(y < x)`
   */
  val minimal = DEF(λ(x, λ(A, λ(<, ∀(y, y ∈ A ==> ¬(y < x))))))

  /**
   * Upper bound --- `x` is an upper bound on `A` with respect to `<` if
   *
   *    `∀ y ∈ A. y < x \/ y = x`
   *
   * Note that `x ∈ A` is not required.
   */
  val upperBound = DEF(λ(x, λ(A, λ(<, ∀(y, y ∈ A ==> (y < x) \/ (y === x))))))

  /**
   * Lower bound --- `x` is a lower bound on `A` with respect to `<` if
   *
   *    `∀ y ∈ A. x < y \/ y = x`
   *
   * Note that `x ∈ A` is not required.
   */
  val lowerBound = DEF(λ(x, λ(A, λ(<, ∀(y, y ∈ A ==> (x < y) \/ (y === x))))))

  /**
   * Greatest element --- `x` is the greatest element of `A` with respect to `<` if `x ∈ A` and
   *
   *    `∀ y ∈ A. y < x \/ y = x`
   *
   * In other words, `x` is an upper bound on `A`.
   */
  val greatest = DEF(λ(x, λ(A, λ(<, (x ∈ A) /\ upperBound(x)(A)(<)))))

  /**
   * Least element --- `x` is the least element of `A` with respect to `<` if `x ∈ A` and
   *
   *    `∀ y ∈ A. x < y \/ y = x`
   *
   * In other words, `x` is a lower bound on `A`.
   */
  val least = DEF(λ(x, λ(A, λ(<, (x ∈ A) /\ lowerBound(x)(A)(<)))))
}
