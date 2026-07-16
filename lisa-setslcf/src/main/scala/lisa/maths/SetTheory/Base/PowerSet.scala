package lisa.maths.SetTheory.Base

import Singleton.singleton
import Symbols._

/**
 * The power set of a set `x` is the set `𝒫(x)` that contains all subsets of
 * `x`.
 *
 * Its existence is guaranteed by the [[powerSetAxiom]].
 *
 * @see [[Subset]]
 */
object PowerSet extends lisa.Main {

  /**
   * Definition --- The power set of `x` is the set `𝒫(x)` containing all subsets of `x`.
   *
   *   `x ∈ 𝒫(y) <=> x ⊆ y`
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
    x ∈ 𝒫(x)
  ) {
    have(thesis) by Tautology.from(membership of (y := x), Subset.reflexivity)
  }

  /**
   * Theorem --- A power set is never empty.
   *
   *    `𝒫(x) ≠ ∅`
   */
  val nonEmpty = Theorem(
    𝒫(x) ≠ ∅
  ) {
    have(thesis) by Cut(setInItsPowerSet, EmptySet.setWithElementNonEmpty of (y := 𝒫(x)))
  }

  /**
   * Theorem --- The power set of the empty set is `{∅}`.
   *
   *    `𝒫(∅) = {∅}`
   */
  val emptySet = Theorem(
    𝒫(∅) === singleton(∅)
  ) {
    have(x ∈ 𝒫(∅) <=> x ∈ singleton(∅)) by Tautology.from(
      membership of (y := ∅),
      Subset.rightEmpty,
      Singleton.membership of (y := x, x := ∅)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The power set `𝒫(x)` is not a subset of `x`.
   *
   *    `𝒫(x) ⊆ x ⊢ ⊥`
   *
   * @see [[FoundationAxiom.selfNonInclusion]]
   */
  val nonInclusion = Theorem(
    𝒫(x) ⊆ x |- ()
  ) {
    have(thesis) by Tautology.from(
      membership of (x := 𝒫(x), y := x),
      FoundationAxiom.selfNonInclusion of (x := 𝒫(x))
    )
  }

  /**
   * Theorem --- The unordered pair `{x, y}` is in `𝒫(z)` if and only if both `x ∈ z` and `y ∈ z`.
   *
   *    `{x, y} ∈ 𝒫(z) <=> x ∈ z ∧ y ∈ z`
   *
   * @see [[Subset.leftUnorderedPair]]
   */
  val unorderedPairMembership = Theorem(
    unorderedPair(x, y) ∈ 𝒫(z) <=> (x ∈ z) /\ (y ∈ z)
  ) {
    have(thesis) by Congruence.from(
      membership of (x := unorderedPair(x, y), y := z),
      Subset.leftUnorderedPair
    )
  }
}
