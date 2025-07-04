package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef.{*, given}

/**
 * A relation between `X` and `Y` is a subset `R` of the [[CartesianProduct]]
 * `X × Y`, where `(x, y) ∈ R` means that `x` is related to `y`.
 *
 * This file defines:
 * - (Binary) relations, homogeneous relations
 * - Relation domain, range and field
 * - Basic properties about relations: reflexivity, symmetry, etc.
 */
object Definitions extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val R = variable[Ind]
  private val X, Y = variable[Ind]

  ///////////////////////////////////////////////////////
  section("Definitions")

  /**
   * Definition --- A set `R` is a relation between `X` and `Y` if `R` is
   * a subset of the Cartesian product `X × Y`.
   *
   *   `relationBetween(R, X, Y) <=> R ⊆ X × Y`
   */
  val relationBetween = DEF(λ(R, λ(X, λ(Y, R ⊆ (X × Y)))))

  /**
   * Definition --- A set `R` is a relation on `X` if `R` only contains pairs
   * of elements of `X`.
   *
   *   `relation(R, X) <=> R ⊆ X × X`
   */
  val relationOn = DEF(λ(R, λ(X, R ⊆ (X × X))))

  /**
   * Definition --- A set `R` is a relation if there exists sets `X` and `Y`
   * such that `R` is a relation between `X` and `Y`.
   *
   *   `relation(R) <=> ∃ X, Y. R ⊆ X × Y`
   */
  val relation = DEF(λ(R, ∃(X, ∃(Y, R ⊆ (X × Y)))))

  extension (x: set) {
    // This notation only works for relation `R`, so we keep it private to this file.
    private infix def R(y: set): Expr[Prop] = (x, y) ∈ Definitions.R
  }

  /**
   * Definition --- The domain of a relation `R` is the set of elements that
   * are related to another element.
   *
   *   `dom(R) = {x ∈ ⋃⋃R | ∃ y. x R y}`
   */
  val dom = DEF(λ(R, { x ∈ ⋃(⋃(R)) | ∃(y, x R y) }))

  /**
   * Definition --- The range of a relation `R` is the set of elements that
   * have an element related to them.
   *
   *   `range(R) = {y ∈ ⋃⋃R | ∃ x. x R y}`
   */
  val range = DEF(λ(R, { y ∈ ⋃(⋃(R)) | ∃(x, x R y) }))

  /**
   * Definition --- The field of a relation `R` is the union of its domain and
   * its range.
   *
   *   `field(R) = dom(R) ∪ range(R)`
   */
  val field = DEF(λ(R, dom(R) ∪ range(R)))

  ///////////////////////////////////////////////////////
  section("Properties")

  /**
   * Reflexive Relation --- Every element relates to itself:
   *
   *   `∀ x ∈ X. x R x`
   */
  val reflexive = DEF(λ(R, λ(X, relationOn(R)(X) /\ ∀(x, x ∈ X ==> (x R x)))))

  /**
   * Irreflexive Relation --- No element is related to itself:
   *
   *   `∀ x. ¬(x R x)`.
   */
  val irreflexive = DEF(λ(R, relation(R) /\ ∀(x, ¬(x R x))))

  /**
   * Anti-reflexive Relation --- Alias for [[irreflexive]].
   */
  val antiReflexive = irreflexive

  /**
   * Symmetric Relation --- If `x` is related to `y` then `y` is related to
   * `x`.
   *
   *   `∀ x, y. x R y ⇔ y R x`
   */
  val symmetric = DEF(λ(R, relation(R) /\ ∀(x, ∀(y, (x R y) <=> (y R x)))))

  /**
   * Asymmetric Relation --- If `x` is related to `y` then `y` is not related
   * to `x`.
   *
   *   `∀ x y. x R y ==> ¬(y R x)`
   */
  val asymmetric = DEF(λ(R, relation(R) /\ ∀(x, ∀(y, (x R y) ==> ¬(y R x)))))

  /**
   * Antisymmetric Relation --- If `x` is related to `y` and vice-versa, then
   * `x = y`.
   *
   *   `∀ x y. x R y ∧ y R x ⇒ y = x`
   */
  val antisymmetric = DEF(λ(R, relation(R) /\ ∀(x, ∀(y, (x R y) /\ (y R x) ==> (x === y)))))

  /**
   * Transitive Relation --- If `x` is related to `y` and `y` is related to `z`, then `x`
   * is related to `z`.
   *
   *   `∀ x y z. x R y ∧ y R z ⇒ x R z`
   */
  val transitive = DEF(λ(R, relation(R) /\ ∀(x, ∀(y, ∀(z, (x R y) /\ (y R z) ==> (x R z))))))

  /**
   * Connected Relation --- For every pair of elements `x, y ∈ X`, either `x` is related to `y`,
   * `y` is related to `x`, or `x = y`.
   *
   *   `∀ x ∈ X, y ∈ X. (x R y) ∨ (y R x) ∨ (x = y)`
   */
  val connected = DEF(λ(R, λ(X, relationOn(R)(X) /\ ∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x R y) \/ (y R x) \/ (x === y))))))

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
  val stronglyConnected = DEF(λ(R, λ(X, relationOn(R)(X) /\ ∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x R y) \/ (y R x))))))

  /**
   * Equivalence Relation --- A relation `R` is an equivalence relation on `X`
   * if it is [[reflexive]], [[symmetric]], and [[transitive]].
   */
  val equivalence = DEF(λ(R, λ(X, reflexive(R)(X) /\ symmetric(R) /\ transitive(R))))

  /**
   * For ordering relations, see [[lisa.maths.SetTheory.Order.Order]].
   */
}
