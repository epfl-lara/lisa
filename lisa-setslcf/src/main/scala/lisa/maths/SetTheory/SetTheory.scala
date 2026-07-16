package lisa.maths.SetTheory

import lisa.maths.SetTheory.Base.Predef._

/**
 * Set Theory Library
 *
 * Develops Zermelo-Fraenkel Set Theory.
 * Uses the following book as the main reference:
 *
 * Jech, Thomas. Set theory: The third millennium edition, revised and expanded.
 * Springer Berlin Heidelberg, 2003.
 * [[https://link.springer.com/book/10.1007/3-540-44761-X]]
 */
object SetTheory extends lisa.Main {

  // Variables
  private val h = variable[Prop]
  private val w, t = variable[Ind]

  // Set relations and function symbols
  private val r = variable[Ind]
  private val p = variable[Ind]

  private val Q = variable[Ind >>: Prop]
  private val R = variable[Ind >>: Ind >>: Prop]

  /**
   * Chapter 1
   */

  /**
   * Axioms of Set Theory
   *
   * See [[SetTheoryLibrary]].
   */

  /**
   * Theorem --- Russel's Paradox
   *
   * Consider a set `x`, that contains every set that is not a member of itself.
   * The existence of `x` leads to a contradiction, for we get that
   *
   *   `x ∈ x <=> x ∉ x`.
   *
   * This paradox forces the current form of the comprehension schema, i.e. `{x ∈ S | φ(x)}`
   * instead of `{x | φ(x)}`.
   */
  val `Russel's paradox` = Theorem(
    ∃(y, ∀(x, x ∈ y <=> x ∉ x)) |- ()
  ) {
    have(y ∈ y <=> y ∉ y |- ()) by Tautology
    thenHave(∀(x, x ∈ y <=> x ∉ x) |- ()) by LeftForall
    thenHave(∃(y, ∀(x, x ∈ y <=> x ∉ x)) |- ()) by LeftExists
  }

  //////////////////////////////////////////////////////////////////////////////
  section("Inductive sets")

  // TODO: This should be moved to its own file.

  /**
   * Successor Function --- Maps a set to its 'successor' in the sense required
   * for an inductive set.
   *
   * `successor: x ↦ x ∪ {x}`
   *
   * @param x set
   */
  val successor = DEF(λ(x, x ∪ singleton(x)))

  /**
   * Inductive set --- A set is inductive if it contains the empty set, and the
   * [[successor]]s of each of its elements.
   *
   * `inductive(x) ⇔ (∅ ∈ x ⋀ ∀ y. y ∈ x ⇒ successor(y) ∈ x)`
   *
   * @param x set
   */
  val inductive = DEF(λ(x, (∅ ∈ x) /\ ∀(y, (y ∈ x) ==> (successor(y) ∈ x))))

  /**
   * Theorem --- There exists an inductive set.
   *
   *    `∃ x. inductive(x)`
   *
   * Equivalent to the Axiom of Infinity ([[infinityAxiom]]). The proof shows
   * that the set obtained by the axiom of infinity is in fact inductive.
   */
  val inductiveSetExists = Theorem(
    ∃(x, inductive(x))
  ) {
    def S(y: Expr[Ind]) = ⋃(unorderedPair(y, unorderedPair(y, y)))
    def infinite(x: Expr[Ind]) = ∅ ∈ x /\ ∀(y, y ∈ x ==> S(y) ∈ x)

    have(y ∈ x ==> successor(y) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Restate
    thenHave(y ∈ x ==> (y ∪ singleton(y)) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Substitute(successor.definition of (x := y))
    thenHave(y ∈ x ==> (y ∪ unorderedPair(y, y)) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Substitute(singleton.definition of (x := y))
    thenHave(y ∈ x ==> S(y) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Substitute(∪.definition of (x := y, y := unorderedPair(y, y)))
    thenHave(∀(y, y ∈ x ==> S(y) ∈ x) |- y ∈ x ==> successor(y) ∈ x) by LeftForall
    thenHave(∀(y, y ∈ x ==> S(y) ∈ x) |- ∀(y, y ∈ x ==> successor(y) ∈ x)) by RightForall
    thenHave(infinite(x) |- inductive(x)) by Tautology.fromLastStep(inductive.definition)
    thenHave(infinite(x) |- ∃(x, inductive(x))) by RightExists
    thenHave(∃(x, infinite(x)) |- ∃(x, inductive(x))) by LeftExists

    have(thesis) by Cut(infinityAxiom, lastStep)
  }

}
