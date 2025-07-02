package lisa.maths.SetTheory.Base

import Singleton.singleton
import Union.∪
import Intersection.{⋂, ∩}
import Comprehension.|

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

      val pairEquality = have(unorderedPair(singleton(a), unorderedPair(a, b)) === unorderedPair(singleton(c), unorderedPair(c, d))) by Congruence.from(
        pair.definition of (x := a, y := b),
        pair.definition of (x := c, y := d)
      )

      // We consider two cases: `a = b` and `a ≠ b`

      // If `a = b` then `{{a}, {a, b}} = {{a}} = {{c}, {c, d}}` and thus
      // both `{a} = {c}` and `{a} = {c, d}`.
      val `case a = b` = have(a === b |- (a === c) /\ (b === d)) subproof {
        assume(a === b)

        // TODO: This should be automated
        sorry
      }

      // If `a ≠ b` then `{a} ≠ {a, b}` and thus `{a, b} = {c, d}` and `{a} = {c}`.
      val `case a ≠ b` = have(a ≠ b |- (a === c) /\ (b === d)) subproof {
        have((unorderedPair(a, a) === unorderedPair(a, b)) <=> (a === b)) by Tautology.from(
          UnorderedPair.extensionality of (c := a, d := a)
        )
        thenHave((singleton(a) === unorderedPair(a, b)) <=> (a === b)) by Substitute(singleton.definition of (x := a))
        thenHave(a ≠ b |- singleton(a) ≠ unorderedPair(a, b)) by Congruence
        sorry
      }

      have(thesis) by Tautology.from(`case a = b`, `case a ≠ b`)
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
    * However, this fails when `a = b`, and returns the [[emptySet]].
    *
    * While the function is defined on all sets, the result on non-pairs may be
    * uninteresting or garbage. Generally expected to be simplified via [[pairSnd]].
    */
  val snd = DEF(λ(p, ⋃({x ∈ ⋃(p) | ⋃(p) ≠ ⋂(p) ==> x ∉ ⋂(p)})))


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
    fst (x, y) === x
  ) {
    have(thesis) by Congruence.from(
      fst.definition of (p := (x, y)),
      intersection,
      Singleton.union,
    )
  }


  /**
    * Theorem --- [[snd]] produces the first element of the pair when applied to a pair.
    *
    *    `snd (x, y) = y`
    */
  val pairSnd = Theorem(
    snd (x, y) === y
  ) {
    have(z ∈ {z ∈ ⋃((x, y)) | ⋃((x, y)) ≠ ⋂((x, y)) ==> z ∉ ⋂((x, y))} <=> (z ∈ ⋃((x, y))) /\ (⋃((x, y)) ≠ ⋂((x, y)) ==> z ∉ ⋂((x, y)))) by Tautology.from(
      Comprehension.membership of (x := z, y := ⋃((x, y)), φ := λ(z, ⋃((x, y)) ≠ ⋂((x, y)) ==> z ∉ ⋂((x, y)))),
    )
    sorry
    /*
    thenHave(z ∈ {z ∈ ⋃((x, y)) | ⋃((x, y)) ≠ ⋂((x, y)) ==> z ∉ ⋂((x, y))} <=> (z ∈ unorderedPair(x, y)) /\ (unorderedPair(x, y) ≠ singleton(x) ==> z ∉ singleton(x))) by Substitute(
      union, intersection
    )
     */
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
