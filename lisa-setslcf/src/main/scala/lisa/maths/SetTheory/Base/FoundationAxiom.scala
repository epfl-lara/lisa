package lisa.maths.SetTheory.Base

import Singleton.singleton
import Symbols._

/**
 * The [[axiomOfFoundation]] states that the membership (∈) relation is well-founded,
 * meaning that there are no infinite descending chains `... ∈ x ∈ x1 ∈ x2 ∈ ...`.
 *
 * In particular, this axiom prohibits self inclusion: it is never the case that `x ∈ x`
 * (see [[WellFounded.selfNonInclusion]] for a proof).
 */
object FoundationAxiom extends lisa.Main {

  /**
   * Theorem --- No set is an element of itself.
   *
   *    `x ∉ x`
   *
   * This is a direct consequence of the [[axiomOfFoundation]].
   */
  val selfNonInclusion = Theorem(
    x ∉ x
  ) {
    // Take X = {x}, and consider the axiom of foundation on it
    val X = singleton(x)
    val `axiom of foundation on X` = ∃(y, (y ∈ X) /\ ∀(z, z ∈ X ==> z ∉ y))

    have(∀(z, z ∈ X ==> z ∉ y) |- ∀(z, z ∈ X ==> z ∉ y)) by Restate
    thenHave(∀(z, z ∈ X ==> z ∉ y) |- y ∈ X ==> y ∉ y) by InstantiateForall(y)
    thenHave((∀(z, z ∈ X ==> z ∉ y), y ∈ X) |- y ∉ y) by Restate
    thenHave((∀(z, z ∈ X ==> z ∉ y), y ∈ X, y === x) |- x ∉ x) by Congruence
    thenHave(y ∈ X /\ ∀(z, z ∈ X ==> z ∉ y) |- x ∉ x) by Tautology.fromLastStep(Singleton.membership)
    thenHave(`axiom of foundation on X` |- x ∉ x) by LeftExists

    have(thesis) by Tautology.from(lastStep, Singleton.nonEmpty, axiomOfFoundation of (x := X))
  }

  /**
   * Theorem --- No Universal Set
   *
   *    `∀ z. z ∈ x ⊢ ⊥`
   *
   * There does not exist a set of all sets. Alternatively, its existence, with
   * the [[comprehensionSchema]] and [[SetTheory.`Russel's paradox`]],
   * produce a contradiction.
   */
  val noUniversalSet = Theorem(
    ∀(z, z ∈ x) |- ()
  ) {
    have(x ∈ x |- ()) by Restate.from(selfNonInclusion)
    thenHave(thesis) by LeftForall
  }

  /**
   * Theorem --- For any set `x` there exists another set `y` that is not in `x`.
   *
   * Follows from the fact that no set is universal ([[noUniversalSet]]).
   */
  val freshElement = Theorem(
    ∃(y, y ∉ x)
  ) {
    have(thesis) by Restate.from(noUniversalSet)
  }

  /**
   * Theorem --- Membership is asymmetric.
   *
   *    `¬(x ∈ y /\ y ∈ x)`
   */
  val membershipAsymmetric = Theorem(
    ¬((x ∈ y) /\ (y ∈ x))
  ) {
    assume(x ∈ y)
    assume(y ∈ x)

    // Consider the set p = {x, y}
    val p = unorderedPair(x, y)

    // p is not the empty set
    have(p ≠ ∅) by Weakening(UnorderedPair.nonEmpty)

    // Since p is not empty, by the axiom of foundation there must exist an inclusion minimal element in p
    val minimalElement = have(∃(z, (z ∈ p) /\ ∀(a, a ∈ p ==> a ∉ z))) by Tautology.from(lastStep, axiomOfFoundation of (x := p))

    // It can only be x or y, but both x ∈ y and y ∈ x
    have((y ∈ p) /\ (y ∈ x)) by Tautology.from(UnorderedPair.rightInPair)
    thenHave(z === x |- (y ∈ p) /\ (y ∈ z)) by Congruence
    val xCase = thenHave(z === x |- ∃(a, (a ∈ p) /\ (a ∈ z))) by RightExists

    have((x ∈ p) /\ (x ∈ y)) by Tautology.from(UnorderedPair.leftInPair)
    thenHave(z === y |- (x ∈ p) /\ (x ∈ z)) by Congruence
    val yCase = thenHave(z === y |- ∃(a, (a ∈ p) /\ (a ∈ z))) by RightExists

    // This is a contradiction
    have(z ∈ p ==> ∃(a, (a ∈ p) /\ (a ∈ z))) by Tautology.from(xCase, yCase, UnorderedPair.membership)
    thenHave(∀(z, z ∈ p ==> ∃(a, (a ∈ p) /\ (a ∈ z)))) by RightForall

    have(thesis) by Tautology.from(lastStep, minimalElement)
  }

}
