package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef.{*, given}

/** A relation between `X` and `Y` is a subset `ℛ` of the [[CartesianProduct]]
  * `X × Y`, where `(x, y) ∈ ℛ` means that `x` is related to `y`.
  *
  * This file defines:
  * - (Binary) relations, homogeneous relations
  * - Relation domain, range and field
  * - Basic properties about relations: reflexivity, symmetry, etc.
  */
object Definitions extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val ℛ = variable[Ind]
  private val X, Y = variable[Ind]

  ///////////////////////////////////////////////////////
  section("Definitions")


  /** Definition --- A set `ℛ` is a relation between `X` and `Y` if `ℛ` is
    * a subset of the Cartesian product `X × Y`.
    *
    *   `relationBetween(ℛ, X, Y) <=> ℛ ⊆ X × Y`
    */
  val relationBetween = DEF(λ(ℛ, λ(X, λ(Y, ℛ ⊆ (X × Y)))))

  /** Definition --- A set `ℛ` is a relation on `X` if `ℛ` only contains pairs
    * of elements of `X`.
    *
    *   `relation(ℛ, X) <=> ℛ ⊆ X × X`
    */
  val relationOn = DEF(λ(ℛ, λ(X, ℛ ⊆ (X × X))))

  /** Definition --- A set `ℛ` is a relation if there exists sets `X` and `Y`
    * such that `ℛ` is a relation between `X` and `Y`.
    *
    *   `relation(ℛ) <=> ∃ X, Y. ℛ ⊆ X × Y`
    */
  val relation = DEF(λ(ℛ, ∃(X, ∃(Y, ℛ ⊆ (X × Y)))))

  extension (x: set) {
    // This notation only works for relation `ℛ`, so we keep it private to this file.
    private infix def ℛ(y: set): Expr[Prop] = (x, y) ∈ Definitions.ℛ
  }

  /** Definition --- The domain of a relation `ℛ` is the set of elements that
    * are related to another element.
    *
    *   `dom(ℛ) = {x ∈ ⋃⋃ℛ | ∃ y. x ℛ y}`
    */
  val dom = DEF(λ(ℛ, { x ∈ ⋃(⋃(ℛ)) | ∃(y, x ℛ y) }))

  /** Definition --- The range of a relation `ℛ` is the set of elements that
    * have an element related to them.
    *
    *   `range(ℛ) = {y ∈ ⋃⋃ℛ | ∃ x. x ℛ y}`
    */
  val range = DEF(λ(ℛ, { y ∈ ⋃(⋃(ℛ)) | ∃(x, x ℛ y) }))

  /** Definition --- The field of a relation `ℛ` is the union of its domain and
    * its range.
    *
    *   `field(ℛ) = dom(ℛ) ∪ range(ℛ)`
    */
  val field = DEF(λ(ℛ, dom(ℛ) ∪ range(ℛ)))


  ///////////////////////////////////////////////////////
  section("Properties")


  /** Reflexive Relation --- Every element relates to itself:
    *
    *   `∀ x ∈ X. x ℛ x`
    */
  val reflexive = DEF(λ(ℛ, λ(X, relationOn(ℛ)(X) /\ ∀(x, x ∈ X ==> (x ℛ x)))))


  /** Irreflexive Relation --- No element is related to itself:
    *
    *   `∀ x. ¬(x ℛ x)`.
    */
  val irreflexive = DEF(λ(ℛ, relation(ℛ) /\ ∀(x, ¬(x ℛ x))))


  /** Anti-reflexive Relation --- Alias for [[irreflexive]].
    */
  val antiReflexive = irreflexive


  /** Symmetric Relation --- If `x` is related to `y` then `y` is related to
    * `x`.
    *
    *   `∀ x, y. x ℛ y ⇔ y ℛ x`
    */
  val symmetric = DEF(λ(ℛ, relation(ℛ) /\ ∀(x, ∀(y, (x ℛ y) <=> (y ℛ x)))))


  /** Asymmetric Relation --- If `x` is related to `y` then `y` is not related
    * to `x`.
    *
    *   `∀ x y. x ℛ y ==> ¬(y ℛ x)`
    */
  val asymmetric = DEF(λ(ℛ, relation(ℛ) /\ ∀(x, ∀(y, (x ℛ y) ==> ¬(y ℛ x)))))


  /** Antisymmetric Relation --- If `x` is related to `y` and vice-versa, then
    * `x = y`.
    *
    *   `∀ x y. x ℛ y ∧ y ℛ x ⇒ y = x`
    */
  val antisymmetric = DEF(λ(ℛ, relation(ℛ) /\ ∀(x, ∀(y, (x ℛ y) /\ (y ℛ x) ==> (x === y)))))


  /** Transitive Relation --- If `x` is related to `y` and `y` is related to `z`, then `x`
    * is related to `z`.
    *
    *   `∀ x y z. x ℛ y ∧ y ℛ z ⇒ x ℛ z`
    */
  val transitive = DEF(λ(ℛ, relation(ℛ) /\ ∀(x, ∀(y, ∀(z, (x ℛ y) /\ (y ℛ z) ==> (x ℛ z))))))


  /** Connected Relation --- For every pair of elements `x, y ∈ X`, either `x` is related to `y`,
    * `y` is related to `x`, or `x = y`.
    *
    *   `∀ x ∈ X, y ∈ X. (x ℛ y) ∨ (y ℛ x) ∨ (x = y)`
    */
  val connected = DEF(λ(ℛ, λ(X, relationOn(ℛ)(X) /\ ∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x ℛ y) \/ (y ℛ x) \/ (x === y))))))


  /** Total Relation --- Alias for [[connected]].
    */
  val total = connected


  /** Strongly Connected Relation --- For every pair of elements `x, y ∈ X`,
    * either `x` is related to `y` or `y` is related to `x`.
    *
    * `∀ x ∈ X, y ∈ X. (x ℛ y) \/ (y ℛ x)`
    *
    * @see [[connected]]
    */
  val stronglyConnected = DEF(λ(ℛ, λ(X, relationOn(ℛ)(X) /\ ∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x ℛ y) \/ (y ℛ x))))))


  /** Equivalence Relation --- A relation `ℛ` is an equivalence relation on `X`
    * if it is [[reflexive]], [[symmetric]], and [[transitive]].
    */
  val equivalence = DEF(λ(ℛ, λ(X, reflexive(ℛ)(X) /\ symmetric(ℛ) /\ transitive(ℛ))))

  /** For ordering relations, see [[lisa.maths.SetTheory.Order.Order]]. */
}
