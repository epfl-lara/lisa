package lisa.maths.SetTheory.Base

import lisa.maths.Quantifiers

import Singleton.singleton
import Symbols._

/**
 * We say that `x` is a subset of `y`, denoted by `x ⊆ y`, if all elements of
 * `x` are elements of `y`.
 *
 * @see [[PowerSet]]
 */
object Subset extends lisa.Main {

  /**
   * Definition --- `x` is a subset of `y`, denoted `x ⊆ y`, if every element of `x` is an element of `y`.
   *
   *   `∀z. z ∈ x ==> z ∈ y`
   *
   * @see [[subsetAxiom]]
   */
  val definition = subsetAxiom

  /**
   * Theorem --- If `x ⊆ y` and `z ∈ x` then `z ∈ y`.
   *
   *   `x ⊆ y |- z ∈ x ==> z ∈ y`
   *
   * Reformulation of the definition.
   */
  val membership = Theorem(
    x ⊆ y |- z ∈ x ==> z ∈ y
  ) {
    have(x ⊆ y |- ∀(z, z ∈ x ==> z ∈ y)) by Tautology.from(definition)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Proper Subset --- `x ⊂ y`. Shorthand for `x ⊆ y ∧ x != y`.
   *
   * @param x Set
   * @param y Set
   */
  val ⊂ = DEF(λ(x, λ(y, x ⊆ y /\ x ≠ y))).printInfix()
  val properSubset = ⊂

  extension (x: Expr[Ind]) {
    inline infix def ⊂(y: Expr[Ind]): Expr[Prop] = properSubset(x)(y)
  }

  /**
   * Theorem --- Subset reflexivity
   *
   * Every set is a subset of itself. In other words, the subset
   * predicate induces a [[reflexive]] [[relation]] on sets.
   */
  val reflexivity = Theorem(
    x ⊆ x
  ) {
    have(x ⊆ x <=> ∀(z, ⊤)) by Restate.from(subsetAxiom of (y := x))
    thenHave(x ⊆ x <=> ⊤) by Substitute(Quantifiers.closedFormulaUniversal)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- The subset predicate is transitive.
   *
   *    `x ⊆ y ∧ y ⊆ z ⊢ x ⊆ z`
   */
  val transitivity = Theorem(
    (x ⊆ y, y ⊆ z) |- x ⊆ z
  ) {
    have((x ⊆ y, y ⊆ z) |- a ∈ x ==> a ∈ z) by Tautology.from(
      membership of (x := x, y := y, z := a),
      membership of (x := y, y := z, z := a)
    )
    thenHave((x ⊆ y, y ⊆ z) |- ∀(a, a ∈ x ==> a ∈ z)) by RightForall
    thenHave(thesis) by Substitute(definition)
  }

  /**
   * Theorem --- Double inclusion: `x = y` if and only if `x ⊆ y` and `y ⊆ x`.
   *
   *  `x = y <=> x ⊆ y /\ y ⊆ x`
   *
   * In other words, `⊆` is antisymmetric.
   */
  val doubleInclusion = Theorem(
    (x === y) <=> (x ⊆ y) /\ (y ⊆ x)
  ) {
    val `==>` = have(x === y |- (x ⊆ y) /\ (y ⊆ x)) subproof {
      assume(x === y)

      val left = have(x ⊆ x |- (x ⊆ y)) by Congruence
      val right = have(x ⊆ x |- (y ⊆ x)) by Congruence

      have(thesis) by Tautology.from(reflexivity, left, right)
    }

    val `<==` = have((x ⊆ y) /\ (y ⊆ x) |- (x === y)) subproof {
      have((x ⊆ y) /\ (y ⊆ x) |- z ∈ x <=> z ∈ y) by Tautology.from(
        membership of (x := x, y := y),
        membership of (x := y, y := x)
      )
      thenHave(thesis) by Extensionality
    }

    have(thesis) by Tautology.from(`==>`, `<==`)
  }
  val antisymmetry = doubleInclusion

  /**
   * Theorem --- The empty set is a subset of every set.
   *
   *    `∅ ⊆ x`
   */
  val leftEmpty = Theorem(
    ∅ ⊆ x
  ) {
    have(y ∈ ∅ ==> y ∈ x) by Weakening(EmptySet.definition of (x := y))
    thenHave(∀(y, y ∈ ∅ ==> y ∈ x)) by RightForall
    have(thesis) by Tautology.from(definition of (x := ∅, y := x), lastStep)
  }

  /**
   * Theorem --- If a set is a subset of the empty set, it is empty.
   *
   *    `x ⊆ ∅ <=> x = ∅`
   */
  val rightEmpty = Theorem(
    x ⊆ ∅ <=> (x === ∅)
  ) {
    val `==>` = have(x ⊆ ∅ |- (x === ∅)) subproof {
      assume(x ⊆ ∅)

      have(z ∉ x) by Tautology.from(membership of (y := ∅), EmptySet.definition of (x := z))
      thenHave(∀(z, z ∉ x)) by RightForall

      have(thesis) by Cut(lastStep, EmptySet.setWithNoElementsIsEmpty)
    }

    val `<==` = have((x === ∅) |- x ⊆ ∅) by Substitute(x === ∅)(leftEmpty of (x := ∅))

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Theorem --- If `{x, y}` is a subset of `z`, then both `x ∈ z` and `y ∈ z`.
   *
   *    `unorderedPair(x, y) ⊆ z <=> (x ∈ z) /\ (y ∈ z)`
   */
  val leftUnorderedPair = Theorem(
    unorderedPair(x, y) ⊆ z <=> (x ∈ z) /\ (y ∈ z)
  ) {
    have(thesis) by Congruence.from(
      ⊆.definition of (x := unorderedPair(x, y), y := z),
      UnorderedPair.universalQuantifier of (P := λ(a, a ∈ z))
    )
  }

  /**
   * Theorem --- `{x}` is a subset of `y` if and only `x ∈ y`.
   */
  val leftSingleton = Theorem(
    singleton(x) ⊆ y <=> (x ∈ y)
  ) {
    have(unorderedPair(x, x) ⊆ y <=> (x ∈ y)) by Tautology.from(leftUnorderedPair of (x := x, y := x, z := y))
    thenHave(thesis) by Substitute(singleton.definition)
  }

}
