package lisa.maths.SetTheory.Base

import Symbols._

/**
 * A singleton is a set of the form `{x}` for some set `x`. The sole element of
 * a singleton `{x}` is `x`.
 *
 * Singletons are obtained from unordered pairs as `{x} = {x, x}`.
 *
 * @see [[UnorderedPair]]
 */
object Singleton extends lisa.Main {

  /**
   * Singleton Set --- `{x}`. Shorthand for `{x, x}`.
   *
   * @param x Set
   */
  val singleton = DEF(λ(x, unorderedPair(x, x))).printAs(args => s"{${args(0)}}")

  /**
   * Theorem --- A set belongs to a [[singleton]] if and only if it is the single element.
   *
   *    `y ∈ {x} <=> y = x`
   *
   * Specializes the [[pairAxiom]] to a singleton.
   */
  val membership = Theorem(
    y ∈ singleton(x) <=> (y === x)
  ) {
    have(y ∈ unorderedPair(x, x) <=> (y === x)) by Restate.from(UnorderedPair.membership of (x := x, y := x, z := y))
    thenHave(thesis) by Substitute(singleton.definition)
  }

  /**
   * Theorem --- A singleton set is never empty.
   *
   *    `{x} ≠ ∅`
   */
  val nonEmpty = Theorem(
    singleton(x) ≠ ∅
  ) {
    have(x ∈ singleton(x)) by Restate.from(membership of (y := x))
    have(thesis) by Cut(lastStep, EmptySet.setWithElementNonEmpty of (y := singleton(x)))
  }

  /**
   * Theorem --- Two singletons are equal iff their elements are equal.
   *
   *    `{x} = {y} <=> x = y`
   */
  val extensionality = Theorem(
    (singleton(x) === singleton(y)) <=> (x === y)
  ) {
    val `==>` = have(singleton(x) === singleton(y) |- (x === y)) subproof {
      assume(singleton(x) === singleton(y))
      have(x ∈ singleton(x) <=> x ∈ singleton(y)) by Congruence
      thenHave(thesis) by Tautology.fromLastStep(
        membership of (x := x, y := x),
        membership of (x := y, y := x)
      )
    }

    val `<==` = have((x === y) |- (singleton(x) === singleton(y))) by Congruence

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Theorem --- `{x} = {y, z}` if and only if `x = y` and `x = z`.
   */
  val equalsUnorderedPair = Theorem(
    (singleton(x) === unorderedPair(y, z)) <=> (x === y) /\ (x === z)
  ) {
    have((unorderedPair(x, x) === unorderedPair(y, z)) <=> (x === y) /\ (x === z)) by Tautology.from(
      UnorderedPair.extensionality of (a := x, b := x, c := y, d := z)
    )
    thenHave(thesis) by Substitute(singleton.definition)
  }

  /**
   * Theorem --- Union of a singleton
   *
   * The unary [[union]] operation unfolds a [[singleton]] into the single
   * element.
   *
   *      `∀ x. ⋃{x} === x`
   */
  val union = Theorem(
    ⋃(singleton(x)) === x
  ) {
    val `==>` = have(z ∈ ⋃(singleton(x)) ==> (z ∈ x)) subproof {
      have((z ∈ y, y === x) |- (z ∈ x)) by Congruence
      thenHave((z ∈ y) /\ (y ∈ singleton(x)) |- (z ∈ x)) by Tautology.fromLastStep(membership)
      thenHave(∃(y, (z ∈ y) /\ (y ∈ singleton(x))) |- (z ∈ x)) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (x := singleton(x)))
    }

    val `<==` = have((z ∈ x) ==> (z ∈ ⋃(singleton(x)))) subproof {
      assume(z ∈ x)
      have(z ∈ x /\ x ∈ singleton(x)) by Tautology.from(membership of (y := x))
      thenHave(∃(y, z ∈ y /\ y ∈ singleton(x))) by RightExists
      thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (x := singleton(x)))
    }

    have((z ∈ ⋃(singleton(x))) <=> (z ∈ x)) by RightIff(`==>`, `<==`)
    thenHave(thesis) by Extensionality
  }
}
