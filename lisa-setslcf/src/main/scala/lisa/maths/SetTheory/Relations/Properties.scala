package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef._

import Relation._

/**
 * This file define important properties about relations:
 * - Reflexivity
 * - Symmetry
 * - Anti-symmetry
 * - Totality
 */
object Properties extends lisa.Main {

  /**
   * Reflexive Relation --- Every element relates to itself:
   *
   *   `∀ x ∈ X. x R x`
   */
  val reflexive = DEF(λ(R, λ(X, ∀(x ∈ X, x R x))))

  /**
   * Irreflexive Relation --- No element is related to itself:
   *
   *   `∀ x ∈ X. ¬(x R x)`
   */
  val irreflexive = DEF(λ(R, λ(X, ∀(x ∈ X, ¬(x R x)))))

  /**
   * Symmetric Relation --- If `x` is related to `y` then `y` is related to
   * `x`.
   *
   *   `∀ x, y ∈ X. x R y ⇔ y R x`
   */
  val symmetric = DEF(λ(R, λ(X, ∀(x ∈ X, ∀(y ∈ X, (x R y) <=> (y R x))))))

  /**
   * Asymmetric Relation --- If `x` is related to `y` then `y` is not related
   * to `x`.
   *
   *   `∀ x, y ∈ X. x R y ==> ¬(y R x)`
   */
  val asymmetric = DEF(λ(R, λ(X, ∀(x ∈ X, ∀(y ∈ X, (x R y) ==> ¬(y R x))))))

  /**
   * Antisymmetric Relation --- If `x` is related to `y` and vice-versa, then
   * `x = y`.
   *
   *   `∀ x, y ∈ X. x R y ∧ y R x ⇒ y = x`
   */
  val antisymmetric = DEF(λ(R, λ(X, ∀(x ∈ X, ∀(y ∈ X, (x R y) /\ (y R x) ==> (x === y))))))

  /**
   * Transitive Relation --- If `x` is related to `y` and `y` is related to `z`, then `x`
   * is related to `z`.
   *
   *   `∀ x, y, z ∈ X. x R y ∧ y R z ⇒ x R z`
   */
  val transitive = DEF(λ(R, λ(X, ∀(x ∈ X, ∀(y ∈ X, ∀(z ∈ X, (x R y) /\ (y R z) ==> (x R z)))))))

  /**
   * Connected Relation --- For every pair of elements `x, y ∈ X`, either `x` is related to `y`,
   * `y` is related to `x`, or `x = y`.
   *
   *   `∀ x ∈ X, y ∈ X. (x R y) ∨ (y R x) ∨ (x = y)`
   */
  val connected = DEF(λ(R, λ(X, ∀(x ∈ X, ∀(y ∈ X, (x R y) \/ (y R x) \/ (x === y))))))

  /**
   * Total Relation --- Alias for [[connected]].
   */
  val total = connected

  /**
   * Strongly Connected Relation --- For every pair of elements `x, y ∈ X`,
   * either `x` is related to `y` or `y` is related to `x`.
   *
   * `∀ x ∈ X, y ∈ X. (x R y) \/ (y R x)`
   *
   * @see [[connected]]
   */
  val stronglyConnected = DEF(λ(R, λ(X, ∀(x ∈ X, ∀(y ∈ X, (x R y) \/ (y R x))))))

  /**
   * Functional --- `R` is said to be functional on `X` if for all `x ∈ X`,
   * whenever `x R y` and `x R z` hold, we must have `y = z`.
   */
  val functional = DEF(λ(R, λ(X, ∀(x ∈ X, ∀(y, ∀(z, (x R y) /\ (x R z) ==> (y === z)))))))

}
