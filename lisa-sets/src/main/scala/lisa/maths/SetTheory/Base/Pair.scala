package lisa.maths.SetTheory.Base

import Singleton.singleton
import Union.∪
import Intersection.{⋂, ∩}
import Comprehension.|

import lisa.maths.Quantifiers

/**
 * The ordered pair `(x, y)` is a pair of elements where order matters:
 * `(x, y) = (x', y')` if and only if `x = x'` and `y = y'`.
 *
 * In terms of sets, `(x, y)` is defined to be equal to `{{x}, {x, y}}`
 * (Kuratowski's definition). This definition satisfies the extensionality
 * property stated above (for a proof, see [[extensionality]]).
 */
object Pair extends lisa.Main {

  private val a, b, c, d = variable[Ind]
  private val x, y, z = variable[Ind]
  private val p = variable[Ind]
  private val P, Q = variable[Ind >>: Prop]

  /**
   * Ordered Pair --- `(x, y)`. Shorthand for `{{x}, {x, y}}` (Kuratowski's definition).
   *
   * @param x set
   * @param y set
   *
   * @see https://en.wikipedia.org/wiki/Ordered_pair#Kuratowski's_definition
   */
  val pair = DEF(λ(x, λ(y, unorderedPair(singleton(x), unorderedPair(x, y))))).printAs(args => s"(${args(0)}, ${args(1)})")

  /**
   * Implicit conversion from Scala pairs to set-theoretic pairs, to match the
   * printed notation.
   *
   * To use this notation, import it as follows:
   * {{{
   * import lisa.maths.SetTheory.Base.Predef.given
   * }}}
   */
  given Conversion[(Expr[Ind], Expr[Ind]), Expr[Ind]] = (x, y) => pair(x)(y)

  /**
   * Pair Extensionality --- Two ordered pairs are equal iff their elements are
   * equal when taken in order.
   *
   *  `(a, b) = (c, d) <=> a = c ∧ b = d`
   */
  val extensionality = Theorem(
    ((a, b) === (c, d)) <=> (a === c) /\ (b === d)
  ) {
    val `==>` = have((a, b) === (c, d) |- (a === c) /\ (b === d)) subproof {
      assume((a, b) === (c, d))

      // This is a work-around Tautology not using Congruence yet
      // Remove once Tautology is powerful enough
      val eqTransitivity = have((a === c, d === a, c === b) |- b === d) by Congruence

      have(unorderedPair(singleton(a), unorderedPair(a, b)) === unorderedPair(singleton(c), unorderedPair(c, d))) by Congruence.from(
        pair.definition of (x := a, y := b),
        pair.definition of (x := c, y := d)
      )
      thenHave(
        ((singleton(a) === singleton(c)) /\ (unorderedPair(a, b) === unorderedPair(c, d))) \/
          ((singleton(a) === unorderedPair(c, d)) /\ (unorderedPair(a, b) === singleton(c)))
      ) by Tautology.fromLastStep(
        UnorderedPair.extensionality of (a := singleton(a), b := unorderedPair(a, b), c := singleton(c), d := unorderedPair(c, d))
      )
      thenHave(thesis) by Tautology.fromLastStep(
        Singleton.extensionality of (x := a, y := c),
        Singleton.equalsUnorderedPair of (x := a, y := c, z := d),
        UnorderedPair.extensionality,
        Singleton.equalsUnorderedPair of (x := c, y := a, z := b),
        eqTransitivity
      )
    }

    val `<==` =
      have((a === c, b === d) |- (a, b) === (c, d)) by Congruence
      thenHave((a === c) /\ (b === d) ==> ((a, b) === (c, d))) by Restate

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * The first element of an ordered [[pair]] --- `fst(p) = ⋃(⋂(p))`
   *
   * If `p = (a, b) = {{a}, {a, b}}`, `⋂p = {a}`, and `⋃⋂p = a`.
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be simplified via [[pairFst]].
   */
  val fst = DEF(λ(p, ⋃(⋂(p))))

  /**
   * The second element of an ordered [[pair]] ---
   *
   *    `snd p = ⋃{x ∈ ⋃p | ⋃p ≠ ⋂p ⟹ x ∉ ⋂p}`
   *
   * There is a more naive definition: `snd p = ⋃(⋃p ∖ (fst p))`
   * If `p = (a, b) = {{a}, {a, b}}`, `⋃ p = {a, b}`, and `⋃p ∖ (fst p)
   * = {a, b} ∖ {a} = {b}`, the `⋃` at the top level reduces to `b`.
   * However, this fails when `a = b`, and returns [[∅]].
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be simplified via [[pairSnd]].
   */
  val snd = DEF(λ(p, ⋃({ x ∈ ⋃(p) | ⋃(p) ≠ ⋂(p) ==> x ∉ ⋂(p) })))

  /**
   * Theorem --- The union of an ordered pair is the corresponding unordered pair.
   *
   *    `⋃(x, y) = ⋃{{x}, {x, y}} = {x, y}`
   */
  val union = Theorem(
    ⋃((x, y)) === unorderedPair(x, y)
  ) {
    have(z ∈ ⋃((x, y)) <=> (z === x) \/ ((z === x) \/ (z === y))) by Congruence.from(
      pair.definition,
      ∪.definition of (x := singleton(x), y := unorderedPair(x, y)),
      Union.membership of (x := singleton(x), y := unorderedPair(x, y)),
      Singleton.membership of (y := z),
      UnorderedPair.membership
    )
    thenHave(z ∈ ⋃((x, y)) <=> z ∈ unorderedPair(x, y)) by Tautology.fromLastStep(UnorderedPair.membership)
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The unary intersection of an ordered pair is the singleton
   * containing the first element.
   *
   *    `⋂(x, y) = ⋂{{x}, {x, y}} = {x}`
   */
  val intersection = Theorem(
    ⋂((x, y)) === singleton(x)
  ) {
    have(z ∈ ⋂((x, y)) <=> (z === x) /\ ((z === x) \/ (z === y))) by Congruence.from(
      pair.definition,
      Intersection.ofUnorderedPair of (x := singleton(x), y := unorderedPair(x, y)),
      Intersection.membership of (x := singleton(x), y := unorderedPair(x, y)),
      Singleton.membership of (y := z),
      UnorderedPair.membership
    )
    thenHave(z ∈ ⋂((x, y)) <=> z ∈ singleton(x)) by Tautology.fromLastStep(Singleton.membership of (y := z))
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- [[fst]] produces the first element of the pair when applied to a pair.
   *
   *    `fst (x, y) = x`
   */
  val pairFst = Theorem(
    fst(x, y) === x
  ) {
    have(thesis) by Congruence.from(
      fst.definition of (p := (x, y)),
      intersection,
      Singleton.union
    )
  }

  /**
   * Theorem --- [[snd]] produces the first element of the pair when applied to a pair.
   *
   *    `snd (x, y) = y`
   */
  val pairSnd = Theorem(
    snd(x, y) === y
  ) {
    val A = { z ∈ ⋃(x, y) | ⋃(x, y) ≠ ⋂(x, y) ==> z ∉ ⋂(x, y) }

    have(z ∈ ⋃(A) <=> ∃(a, a ∈ A /\ (z ∈ a))) by Tautology.from(unionAxiom of (x := A))
    val definition = thenHave(z ∈ snd(x, y) <=> ∃(a, a ∈ A /\ (z ∈ a))) by Substitute(snd.definition of (p := (x, y)))

    have(a ∈ A <=> a ∈ ⋃(x, y) /\ (⋃(x, y) ≠ ⋂(x, y) ==> a ∉ ⋂(x, y))) by Comprehension.apply
    have(a ∈ A <=> a ∈ unorderedPair(x, y) /\ (unorderedPair(x, y) ≠ singleton(x) ==> a ∉ singleton(x))) by Congruence.from(lastStep, union, intersection)
    val `a ∈ A` = thenHave(a ∈ A <=> ((a === x) \/ (a === y)) /\ (x ≠ y ==> (a ≠ x))) by Tautology.fromLastStep(
      UnorderedPair.membership of (z := a),
      Singleton.equalsUnorderedPair of (y := x, z := y),
      Singleton.membership of (y := a)
    )
    thenHave(a ∈ A <=> ((a === x) \/ (a === y)) /\ ((a === x) ==> (x === y))) by Tautology

    // We must treat these cases separately since Tautology does not apply Congruence
    val case1 = have((a === x, x === y) |- a === y) by Congruence
    val case2 = have((a === x, a === y) |- x === y) by Congruence

    have(a ∈ A /\ (z ∈ a) <=> (z ∈ a) /\ (a === y)) by Tautology.from(`a ∈ A`, case1, case2)
    thenHave(∀(a, a ∈ A /\ (z ∈ a) <=> (z ∈ a) /\ (a === y))) by RightForall
    thenHave(∃(a, a ∈ A /\ (z ∈ a)) <=> ∃(a, (z ∈ a) /\ (a === y))) by Tautology.fromLastStep(
      Quantifiers.existentialEquivalenceDistribution of (P := λ(a, a ∈ A /\ (z ∈ a)), Q := λ(a, z ∈ a /\ (a === y)))
    )
    thenHave(∃(a, a ∈ A /\ (z ∈ a)) <=> z ∈ y) by Substitute(Quantifiers.onePointRule)

    have(z ∈ snd(x, y) <=> z ∈ y) by Tautology.from(lastStep, definition)
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- If `x` is a pair then `x = (fst(x), snd(x))`
   *
   *    `x = (fst(x), snd(x))`
   */
  val pairReconstruction = Theorem(
    x === (a, b) |- (x === (fst(x), snd(x)))
  ) {
    have(thesis) by Congruence.from(
      pairFst of (x := a, y := b),
      pairSnd of (x := a, y := b)
    )
  }
}
