package lisa.maths.SetTheory.Base

import Singleton.singleton
import Subset.⊂

/**
 * The power set of a set `x` is the set `power(x)` that contains all subsets of
 * `x`.
 *
 * Its existence is guaranteed by the [[powerSetAxiom]].
 *
 * @see [[Subset]]
 */
object PowerSet extends lisa.Main {

  private val x, y, z = variable[Ind]

  /**
   * Definition --- The power set of `x` is the set `power(x)` containing all subsets of `x`.
   *
   *   `x ∈ power(y) <=> x ⊆ y`
   *
   * Its existence is guaranteed by the [[powerSetAxiom]].
   */
  val membership = powerSetAxiom

  /**
   * Theorem --- Every set is a member of its power set.
   *
   *    `x ∈ power(x)`
   */
  val setInItsPowerSet = Theorem(
    x ∈ power(x)
  ) {
    have(thesis) by Tautology.from(membership of (y := x), Subset.reflexivity)
  }

  /**
   * Theorem --- A power set is never empty.
   *
   *    `power(x) ≠ ∅`
   */
  val nonEmpty = Theorem(
    power(x) ≠ ∅
  ) {
    have(thesis) by Cut(setInItsPowerSet, EmptySet.setWithElementNonEmpty of (y := power(x)))
  }

  /**
   * Theorem --- The power set of the empty set is `{∅}`.
   *
   *    `power(∅) = {∅}`
   */
  val emptySet = Theorem(
    power(∅) === singleton(∅)
  ) {
    have(x ∈ power(∅) <=> x ∈ singleton(∅)) by Tautology.from(
      membership of (y := ∅),
      Subset.rightEmpty,
      Singleton.membership of (y := x, x := ∅)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The power set `power(x)` is not a subset of `x`.
   *
   *    `power(x) ⊆ x ⊢ ⊥`
   *
   * @see [[WellFounded.selfNonInclusion]]
   */
  val nonInclusion = Theorem(
    power(x) ⊆ x |- ()
  ) {
    have(thesis) by Tautology.from(
      membership of (x := power(x), y := x),
      WellFounded.selfNonInclusion of (x := power(x))
    )
  }

  /**
   * Theorem --- The unordered pair `{x, y}` is in `power(z)` if and only if both `x ∈ z` and `y ∈ z`.
   *
   *    `{x, y} ∈ power(z) <=> x ∈ z ∧ y ∈ z`
   *
   * @see [[Subset.leftUnorderedPair]]
   */
  val unorderedPairMembership = Theorem(
    unorderedPair(x, y) ∈ power(z) <=> (x ∈ z) /\ (y ∈ z)
  ) {
    have(thesis) by Congruence.from(
      membership of (x := unorderedPair(x, y), y := z),
      Subset.leftUnorderedPair
    )
  }
}
