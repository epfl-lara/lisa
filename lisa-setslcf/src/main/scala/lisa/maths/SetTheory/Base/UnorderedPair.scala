package lisa.maths.SetTheory.Base

import Symbols._

/**
 * `{x, y}` is the unordered pair of `x` and `y`. It is written in LISA as
 * `unorderedPair(x, y)`.
 *
 * The pair `{x, y}` is unordered in the sense that `{x, y} = {y, x}`, i.e., the
 * order is irrelevant (see [[UnorderedPair.symmetry]]).
 *
 * The existence of unordered pairs is guaranteed by the [[pairAxiom]].
 */
object UnorderedPair extends lisa.Main {

  /**
   * Theorem --- Unordered pair membership
   *
   *    `z ∈ {x, y} <=> z = x \/ z = y`
   *
   * Also known as the [[pairAxiom]].
   */
  val membership = pairAxiom

  /**
   * Theorem --- The left element is a member of the unordered pair.
   *
   *    `x ∈ {x, y}`
   */
  val leftInPair = Theorem(
    x ∈ unorderedPair(x, y)
  ) {
    have(thesis) by Tautology.from(membership of (z := x))
  }

  /**
   * Theorem --- The right element is a member of the unordered pair.
   *
   *    `y ∈ {x, y}`
   */
  val rightInPair = Theorem(
    y ∈ unorderedPair(x, y)
  ) {
    have(thesis) by Tautology.from(membership of (z := y))
  }

  /**
   * Theorem --- Unordered pairs are non-empty.
   *
   *    `{x, y} ≠ ∅`
   */
  val nonEmpty = Theorem(
    unorderedPair(x, y) ≠ ∅
  ) {
    have(thesis) by Tautology.from(leftInPair, EmptySet.setWithElementNonEmpty of (x := x, y := unorderedPair(x, y)))
  }

  /**
   * Theorem --- The [[unorderedPair]] is, in fact, unordered.
   *
   *    `{x, y} = {y, x}`
   */
  val symmetry = Theorem(
    unorderedPair(x, y) === unorderedPair(y, x)
  ) {
    have((z ∈ unorderedPair(x, y)) <=> (z ∈ unorderedPair(y, x))) by Tautology.from(
      membership of (x := x, y := y),
      membership of (x := y, y := x)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- Two [[unorderedPair]] are equal if and only if their elements match.
   *
   *    `{a, b} = {c, d} <=> (a = c /\ b = d) \/ (a = d /\ b = c)`
   */
  val extensionality = Theorem(
    (unorderedPair(a, b) === unorderedPair(c, d)) <=> ((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))
  ) {
    val p1 = unorderedPair(a, b)
    val p2 = unorderedPair(c, d)

    val `==>` = have((p1 === p2) |- ((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))) subproof {
      assume(p1 === p2)

      have(z ∈ p1 <=> z ∈ p2) by Congruence
      thenHave((z === a) \/ (z === b) <=> (z === c) \/ (z === d)) by Tautology.fromLastStep(
        membership of (x := a, y := b),
        membership of (x := c, y := d)
      )

      have(thesis) by Tautology.from(
        lastStep of (z := a),
        lastStep of (z := b),
        lastStep of (z := c),
        lastStep of (z := d)
      )
    }

    val `<==` = have(((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)) |- (p1 === p2)) subproof {
      val leftCase = have((a === c, b === d) |- (p1 === p2)) by Congruence
      val rightCase = have((a === d, b === c) |- (p1 === p2)) by Congruence.from(symmetry of (x := a, y := b))

      have(thesis) by Tautology.from(leftCase, rightCase)
    }

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Universal quantifier elimination ---
   *
   *   `∀z ∈ {x, y} P(z)` is equivalent to `P(x) /\ P(y)`.
   */
  val universalQuantifier = Theorem(
    ∀(z ∈ unorderedPair(x, y), P(z)) <=> P(x) /\ P(y)
  ) {
    val `==>` = have(∀(z ∈ unorderedPair(x, y), P(z)) |- P(x) /\ P(y)) subproof {
      assume(∀(z ∈ unorderedPair(x, y), P(z)))
      thenHave(z ∈ unorderedPair(x, y) ==> P(z)) by InstantiateForall(z)
      thenHave((z === x) \/ (z === y) ==> P(z)) by Substitute(membership)
      have(thesis) by Tautology.from(lastStep of (z := x), lastStep of (z := y))
    }

    val `<==` = have((P(x), P(y)) |- ∀(z ∈ unorderedPair(x, y), P(z))) subproof {
      assume(P(x))
      assume(P(y))

      val xCase = have(z === x |- P(z)) by Congruence
      val yCase = have(z === y |- P(z)) by Congruence

      have((z === x) \/ (z === y) |- P(z)) by LeftOr(xCase, yCase)
      thenHave(z ∈ unorderedPair(x, y) |- P(z)) by Substitute(membership)
      thenHave(z ∈ unorderedPair(x, y) ==> P(z)) by Restate
      thenHave(thesis) by RightForall
    }

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Existential quantifier elimination ---
   *
   *   `∃z ∈ {x, y} P(z)` is equivalent to `P(x) \/ P(y)`.
   */
  val existentialQuantifier = Theorem(
    ∃(z ∈ unorderedPair(x, y), P(z)) <=> P(x) \/ P(y)
  ) {
    val `==>` = have(∃(z ∈ unorderedPair(x, y), P(z)) |- P(x) \/ P(y)) subproof {
      val xCase = have((P(z), z === x) |- P(x)) by Congruence
      val yCase = have((P(z), z === y) |- P(y)) by Congruence

      have(z ∈ unorderedPair(x, y) /\ P(z) |- P(x) \/ P(y)) by Tautology.from(
        xCase,
        yCase,
        membership
      )
      thenHave(thesis) by LeftExists
    }

    val `<==` = have(P(x) \/ P(y) |- ∃(z ∈ unorderedPair(x, y), P(z))) subproof {
      val xCase =
        have(P(x) |- x ∈ unorderedPair(x, y) /\ P(x)) by Tautology.from(leftInPair)
        thenHave(P(x) |- ∃(z ∈ unorderedPair(x, y), P(z))) by RightExists

      val yCase =
        have(P(y) |- y ∈ unorderedPair(x, y) /\ P(y)) by Tautology.from(rightInPair)
        thenHave(P(y) |- ∃(z ∈ unorderedPair(x, y), P(z))) by RightExists

      have(thesis) by LeftOr(xCase, yCase)
    }

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

}
