package lisa.maths.SetTheory.Base

import Symbols.*

/**
 * The union of two sets `x` and `y` is the set `x ∪ y` that contains all
 * elements of `x`, and all elements of `y`.
 *
 * More generally, the union of a collection of sets `S` is the set `⋃S` that
 * contains all sets that are in any set of `S`.
 *
 * The existence of `⋃S` for any `S` is guaranteed by the [[unionAxiom]].
 */
object Union extends lisa.Main {

  /**
   * Binary Set ⋃ --- `x ∪ y = ⋃{x, y}`
   *
   * @param x set
   * @param y set
   */
  val ∪ = DEF(λ(x, λ(y, ⋃(unorderedPair(x, y))))).printInfix()
  val setUnion = ∪

  extension (x: Expr[Ind]) {

    /**
     * Infix notation for `x ∪ y`.
     */
    inline infix def ∪(y: Expr[Ind]): Expr[Ind] = setUnion(x)(y)
  }

  /**
   * Theorem --- `z` is an element of `x ∪ y` iff it is an element of `x` or `y`.
   *
   *   `z ∈ (x ∪ y) <=> z ∈ x \/ z ∈ y`
   */
  val membership = Theorem(
    z ∈ (x ∪ y) <=> (z ∈ x) \/ (z ∈ y)
  ) {
    have(z ∈ ⋃(unorderedPair(x, y)) <=> ∃(a, (z ∈ a) /\ (a ∈ unorderedPair(x, y)))) by Restate.from(unionAxiom of (x := unorderedPair(x, y)))
    thenHave(z ∈ (x ∪ y) <=> ∃(a, (z ∈ a) /\ (a ∈ unorderedPair(x, y)))) by Substitute(∪.definition)
    thenHave(z ∈ (x ∪ y) <=> ∃(a, (a ∈ unorderedPair(x, y)) /\ (z ∈ a))) by Tableau
    thenHave(thesis) by Substitute(UnorderedPair.existentialQuantifier)
  }

  /**
   * Theorem --- a set is an element of `x ∪ y` iff it is an element of `x` or `y`
   *
   *   `z ∈ (x ∪ y) <=> z ∈ x \/ z ∈ y`
   */
  val commutativity = Theorem(
    x ∪ y === y ∪ x
  ) {
    have(z ∈ (x ∪ y) <=> z ∈ (y ∪ x)) by Tautology.from(
      membership of (x := x, y := y),
      membership of (x := y, y := x)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- `∪` is associative:
   *
   *   `(x ∪ y) ∪ z = x ∪ (y ∪ z)`
   */
  val associativity = Theorem(
    (x ∪ y) ∪ z === x ∪ (y ∪ z)
  ) {
    have(a ∈ ((x ∪ y) ∪ z) <=> a ∈ (x ∪ (y ∪ z))) by Tautology.from(
      membership of (x := x, y := y, z := a),
      membership of (x := (x ∪ y), y := z, z := a),
      membership of (x := x, y := (y ∪ z), z := a),
      membership of (x := y, y := z, z := a)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- `∪` is idempotent, i.e. `x ∪ x = x`.
   */
  val idempotence = Theorem(
    x ∪ x === x
  ) {
    have(z ∈ (x ∪ x) <=> z ∈ x) by Tautology.from(membership of (y := x))
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- `x` is a subset of `x ∪ y`.
   *
   *   `x ⊆ x ∪ y`
   */
  val leftSubset = Theorem(
    x ⊆ (x ∪ y)
  ) {
    have(z ∈ x ==> z ∈ (x ∪ y)) by Tautology.from(membership)
    thenHave(∀(z, z ∈ x ==> z ∈ (x ∪ y))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := x, y := (x ∪ y)))
  }

  /**
   * Theorem --- `y` is a subset of `x ∪ y`.
   *
   *   `y ⊆ x ∪ y`
   */
  val rightSubset = Theorem(
    y ⊆ (x ∪ y)
  ) {
    have(y ⊆ (y ∪ x)) by Restate.from(leftSubset of (x := y, y := x))
    thenHave(thesis) by Substitute(commutativity)
  }

  /**
    * Theorem --- If `y ∈ x` then `y ⊆ ⋃x`.
    */
  val subset = Theorem(
    y ∈ x |- y ⊆ ⋃(x)
  ) {
    assume(y ∈ x)
    have(z ∈ y |- (y ∈ x) /\ (z ∈ y)) by Tautology
    thenHave(z ∈ y |- ∃(y ∈ x, z ∈ y)) by RightExists
    thenHave(z ∈ y |- z ∈ ⋃(x)) by Substitute(⋃.definition)
    thenHave(z ∈ y ==> (z ∈ ⋃(x))) by Restate
    thenHave(∀(z, z ∈ y ==> (z ∈ ⋃(x)))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := y, y := ⋃(x)))
  }

  /**
   * Theorem --- If `x ⊆ y` then `(x ∪ z) ⊆ (y ∪ z)`, i.e., the function `_ ∪ z` is monotonic.
   *
   *   `x ⊆ y ==> (x ∪ z) ⊆ (y ∪ z)
   */
  val leftMonotonic = Theorem(
    x ⊆ y |- (x ∪ z) ⊆ (y ∪ z)
  ) {
    assume(x ⊆ y)
    have(a ∈ (x ∪ z) ==> (a ∈ y) \/ (a ∈ z)) by Tautology.from(
      membership of (z := a, x := x, y := z),
      Subset.membership of (z := a)
    )
    thenHave(a ∈ (x ∪ z) ==> a ∈ (y ∪ z)) by Substitute(membership)
    thenHave(∀(a, a ∈ (x ∪ z) ==> a ∈ (y ∪ z))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition)
  }

  /**
   * Theorem --- If `x ⊆ y` then `(z ∪ x) ⊆ (z ∪ x)`, i.e., the function `z ∪ _` is monotonic.
   *
   *   `x ⊆ y ==> (z ∪ x) ⊆ (z ∪ y)
   */
  val rightMonotonic = Theorem(
    x ⊆ y |- (z ∪ x) ⊆ (z ∪ y)
  ) {
    have(thesis) by Congruence.from(
      leftMonotonic,
      commutativity of (x := x, y := z),
      commutativity of (x := y, y := z)
    )
  }

  /**
   * Theorem --- If `x ⊆ a` and `y ⊆ b` then `(x ∪ y) ⊆ (a ∪ b)`.
   *
   * Combination of [[leftMonotonic]] and [[rightMonotonic]].
   */
  val monotonic = Theorem(
    (x ⊆ a, y ⊆ b) |- (x ∪ y) ⊆ (a ∪ b)
  ) {
    have(thesis) by Tautology.from(
      leftMonotonic of (x := x, y := a, z := y),
      rightMonotonic of (x := y, y := b, z := a),
      Subset.transitivity of (x := (x ∪ y), y := (a ∪ y), z := (a ∪ b))
    )
  }

  /**
   * Theorem --- The union preserves the subset relation on the left.
   *
   *   `x ⊆ z /\ y ⊆ z ==> x ∪ y ⊆ z`
   */
  val leftUnionSubset = Theorem(
    (x ⊆ z, y ⊆ z) |- (x ∪ y) ⊆ z
  ) {
    assume(x ⊆ z)
    assume(y ⊆ z)
    have(a ∈ (x ∪ y) ==> (a ∈ x) \/ (a ∈ y)) by Tautology.from(membership of (z := a))
    thenHave(a ∈ (x ∪ y) ==> (a ∈ z)) by Tautology.fromLastStep(
      Subset.membership of (x := x, y := z, z := a),
      Subset.membership of (x := y, y := z, z := a)
    )
    thenHave(∀(a, a ∈ (x ∪ y) ==> (a ∈ z))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition)
  }

  /**
   * Theorem --- The unary union preserves the subset relation on the left.
   *
   *   `∀y ∈ x. y ⊆ z |- ⋃x ⊆ z`
    *
    * Generalization of [[leftUnionSubset]].
   */
  val leftUnaryUnionSubset = Theorem(
    ∀(y ∈ x, y ⊆ z) |- ⋃(x) ⊆ z
  ) {
    assume(∀(y ∈ x, y ⊆ z))
    thenHave(y ∈ x |- y ⊆ z) by InstantiateForall(y)
    thenHave(y ∈ x |- ∀(a, a ∈ y ==> a ∈ z)) by Substitute(⊆.definition of (x := y, y := z))
    thenHave((y ∈ x, a ∈ y) |- a ∈ z) by InstantiateForall(a)
    thenHave((a ∈ y) /\ (y ∈ x) |- a ∈ z) by Restate
    thenHave(∃(y, (a ∈ y) /\ (y ∈ x)) |- a ∈ z) by LeftExists
    thenHave(a ∈ ⋃(x) ==> a ∈ z) by Tautology.fromLastStep(⋃.definition of (z := a))
    thenHave(∀(a ∈ ⋃(x), a ∈ z)) by RightForall
    thenHave(thesis) by Substitute(⊆.definition)
  }

  /**
   * Theorem --- `⋃∅ = ∅`.
   */
  val empty = Theorem(
    ⋃(∅) === ∅
  ) {
    have((y ∈ ∅) /\ (z ∈ y) |- ()) by Tautology.from(EmptySet.definition of (x := y))
    thenHave(∃(y, (y ∈ ∅) /\ (z ∈ y)) |- ()) by LeftExists
    thenHave(z ∈ ⋃(∅) <=> z ∈ ∅) by Tautology.fromLastStep(unionAxiom of (x := ∅), EmptySet.definition of (x := z))
    thenHave(thesis) by Extensionality
  }

}
