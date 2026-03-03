package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.Quantifiers
import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Relations

import Extrema._
import PartialOrder._
import WellOrder._
import InitialSegment._

/**
 * This file is dedicated to proving the well-ordered recursion theorem:
 * Given a well-order `(A, <)`, one can build a function `G` by recursion over
 * `A` that satisfies the following formula:
 *
 *   `G(x) = F(x, G↾initialSegment(x, A, <))` for all `x ∈ A`
 *
 * where `F : V × V -> V` is a class function, and `initialSegment(x, A, <) = {y ∈ A | y < x}`.
 */
object WellOrderedRecursion extends lisa.Main {

  private val F = variable[Ind >>: Ind >>: Ind]
  private val G, G1, G2 = variable[Ind]
  private val S = variable[Ind]
  private val p = variable[Ind]
  private val 𝓕 = variable[Ind]

  extension (f: Expr[Ind]) {
    private def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * The proof is divided into 2 parts: uniqueness and existence.
   *
   * Uniqueness ([[uniqueness]]): follows from well-foundedness of
   * `(A, <)`, from a minimal counterexample to `G1(x) = G2(x)`.
   *
   * Existence ([[existence]]):
   *
   * 1. ([[recursion]])
   *    We first construct a unique approximation `G_x` with domain `A_<x`
   *    for all `x ∈ A`. Namely, we show that
   *
   *      `∀x ∈ A. ∃!G_x. ∀y < x. G_x(y) = F(y, G_x ↾ initialSegment(y, A, <))`
   *
   *    We show unique existence by well-ordered induction: given that there exists
   *    unique approximations `G_y` for all `y < x`, we construct an approximation
   *    `G_x` until `x`, and show that it is unique ([[recursionStep]]).
   *
   *    The approximation `G_x` is constructed as follows ([[recursionStepExistence]]):
   *
   *      Sucessor case ([[successorCase]]):
   *       If `x` has a predecessor `p`, set `G_x = G_p ∪ {(p, F(p, G_p))}`.
   *       Hence `G_x` is an extension of `G_p` with domain `dom(G_x) = A_<p ∪
   *       {p} = A_<x`.
   *
   *      Limit case ([[limitCase]]):
   *       If `x` has no predecessors (i.e. `x` is limit), set `G_x = ⋃{G_y | y
   *       < x}`. `G_x` is a function by virtue of the fact that any two
   *       approximations `G_y` and `G_z` are coherent on the intersection of
   *       their domains ([[coherence]]).
   *
   *    The uniqueness proof for `G_x` is similar to the uniqueness proof above
   *    ([[recursionStepUniqueness]]).
   *
   * 2. ([[existence]])
   *    To define the function over `A`, we take `G = ⋃{G_x | x ∈ A}`, and we show
   *    that it is a function, in a similar fashion as in 1.b (using [[coherence]]).
   *    If there is a maximal element `m ∈ A`, we take `G' = G ∪ {(m, F(m, G))}` instead.
   */

  //////////////////////////////////////////////////////////////
  section("Uniqueness")

  /**
   * Well-ordered recursion function is unique --- If `G1 : A -> V` and `G2 : A -> V`
   * satisfy the recursion equations, then `G1 = G2`.
   *
   * *Proof*:
   *
   * The proof goes by *minimal counter-example*: consider the set
   *
   *   `D = {x ∈ X | G1(x) ≠ G2(x)}`
   *
   * Assume towards a contradiction that `D ≠ ∅`. Then there exists a
   * `<`-minimal element `x ∈ D` such that
   *
   *   `G1(x) ≠ G2(x)` and `G1(y) = G2(y)` for all `y < x`.
   *
   * But this implies that `G1 ↾ A_<x = G2 ↾ A_<x` and hence by definition
   *
   *   `G1(x) = F(x, G1 ↾ A_<x) = F(x, G2 ↾ A_<x) = G2(x)`,
   *
   * Contradiction.
   */
  val uniqueness = Theorem(
    (
      wellOrder(A)(<),
      functionOn(G1)(A),
      functionOn(G2)(A),
      ∀(x ∈ A, G1(x) === F(x)(G1 ↾ initialSegment(x)(A)(<))),
      ∀(x ∈ A, G2(x) === F(x)(G2 ↾ initialSegment(x)(A)(<)))
    ) |- ∀(x ∈ A, G1(x) === G2(x))
  ) {
    assume(wellOrder(A)(<))

    assume(functionOn(G1)(A))
    assume(∀(x ∈ A, G1(x) === F(x)(G1 ↾ initialSegment(x)(A)(<))))
    val `G1(x)` = thenHave(x ∈ A |- G1(x) === F(x)(G1 ↾ initialSegment(x)(A)(<))) by InstantiateForall(x)

    assume(functionOn(G2)(A))
    assume(∀(x ∈ A, G2(x) === F(x)(G2 ↾ initialSegment(x)(A)(<))))
    val `G2(x)` = thenHave(x ∈ A |- G2(x) === F(x)(G2 ↾ initialSegment(x)(A)(<))) by InstantiateForall(x)

    // Consider the set D = { x ∈ A | G1(x) ≠ G2(x) }
    val D = { x ∈ A | G1(x) ≠ G2(x) }
    val `x ∈ D` = have(x ∈ D <=> x ∈ A /\ (G1(x) ≠ G2(x))) by Comprehension.apply

    // Assume towards a contradiction that D ≠ ∅
    have(D ≠ ∅ |- ⊥) subproof {
      assume(D ≠ ∅)

      // Let `x ∈ D` be the `<`-minimal element of D.
      // We have that G1 and G2 agree on initialSegment(x, A, <)
      have(minimal(x)(D)(<) |- (G1 ↾ initialSegment(x)(A)(<)) === (G2 ↾ initialSegment(x)(A)(<))) subproof {
        assume(minimal(x)(D)(<))

        have(∀(y ∈ D, ¬(y < x))) by Tautology.from(minimal.definition of (a := x, A := D))
        thenHave(y ∈ D ==> ¬(y < x)) by InstantiateForall(y)
        thenHave(y ∈ initialSegment(x)(A)(<) ==> (G1(y) === G2(y))) by Tautology.fromLastStep(
          `x ∈ D` of (x := y),
          InitialSegment.membership
        )
        thenHave(∀(y ∈ initialSegment(x)(A)(<), G1(y) === G2(y))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(
          Restriction.extensionality of (A := initialSegment(x)(A)(<), f := G1, g := G2),
          Functions.BasicTheorems.functionOnIsFunction of (f := G1),
          Functions.BasicTheorems.functionOnIsFunction of (f := G2)
        )
      }

      // By definition of G1(x) and G2(x), this means that G1(x) === G2(x)
      have((x ∈ A, minimal(x)(D)(<)) |- G1(x) === G2(x)) by Congruence.from(
        `G1(x)`,
        `G2(x)`,
        lastStep
      )

      // Contradiction since x ∈ D implies G1(x) ≠ G2(x)
      thenHave(minimal(x)(D)(<) |- ()) by Tautology.fromLastStep(
        minimal.definition of (a := x, A := D),
        `x ∈ D`
      )
      thenHave(∃(x, minimal(x)(D)(<)) |- ()) by LeftExists

      // Conclude by well-foundedness
      thenHave(thesis) by Tautology.fromLastStep(
        wellOrder.definition,
        WellFoundedRelation.minimalElement of (R := <, S := D, X := A),
        Comprehension.subset of (y := A, φ := λ(x, G1(x) ≠ G2(x)))
      )
    }

    // Therefore D = ∅
    thenHave(D === ∅) by Restate

    // Hence G1 and G2 agree on A
    have(x ∉ D) by Congruence.from(EmptySet.definition, lastStep)
    thenHave(x ∈ A ==> (G1(x) === G2(x))) by Tautology.fromLastStep(`x ∈ D`)
    thenHave(thesis) by RightForall
  }

  //////////////////////////////////////////////////////////////
  section("Existence")

  /**
   * Definition --- `g` is called an approximation of `G` if
   * 1. `dom(g) = A_<x` for some `x ∈ A`
   * 2. For all `x ∈ dom(g)` we have `g(x) = F(x, g ↾ A_<x)`
   *
   * `g` is an approximation until `x ∈ A` if `dom(g) = A_<x`.
   */
  private def approximation(g: Expr[Ind]): Expr[Prop] =
    ∃(x, approximationUntil(g, x))
  private def approximationUntil(g: Expr[Ind], x: Expr[Ind]): Expr[Prop] =
    (x ∈ A) /\ functionOn(g)(initialSegment(x)(A)(<)) /\ ∀(a ∈ initialSegment(x)(A)(<), g(a) === F(a)(g ↾ initialSegment(a)(A)(<)))

  /**
   * Lemma --- If `f` is an approximation then `f` is a function.
   */
  val approximationIsFunction = Lemma(
    approximation(f) |- function(f)
  ) {
    have(approximationUntil(f, x) |- function(f)) by Tautology.from(Functions.BasicTheorems.functionOnIsFunction of (A := initialSegment(x)(A)(<)))
    thenHave(thesis) by LeftExists
  }

  /**
   * Lemma --- The domain of an approximation is a subset of A.
   */
  val approximationDomain = Lemma(
    approximation(f) |- dom(f) ⊆ A
  ) {
    have((approximationUntil(f, x), x ∈ A) |- dom(f) ⊆ A) by Congruence.from(
      Functions.BasicTheorems.functionOnDomain of (A := initialSegment(x)(A)(<)),
      InitialSegment.subset
    )
    thenHave(approximationUntil(f, x) |- dom(f) ⊆ A) by Tautology
    thenHave(thesis) by LeftExists
  }

  /**
   * Lemma --- If `f` is an approximation until `x` then `f(y) = F(y, f ↾ initialSegment(y, A, <))`
   * for all `y ∈ A_<x`.
   */
  val approximationUntilApp = Lemma(
    (approximationUntil(f, x), y ∈ initialSegment(x)(A)(<)) |- f(y) === F(y)(f ↾ initialSegment(y)(A)(<))
  ) {
    assume(approximationUntil(f, x))

    have(∀(y ∈ initialSegment(x)(A)(<), f(y) === F(y)(f ↾ initialSegment(y)(A)(<)))) by Tautology
    thenHave(thesis) by InstantiateForall(y)
  }

  /**
   * Lemma --- If `f` is an approximation then `f(x) = F(x, f ↾ initialSegment(x, A, <))`
   * for all `x ∈ dom(f)`.
   */
  val approximationApp = Lemma(
    approximation(f) |- ∀(x ∈ dom(f), f(x) === F(x)(f ↾ initialSegment(x)(A)(<)))
  ) {
    val `dom(f)` = have(approximationUntil(f, y) |- dom(f) === initialSegment(y)(A)(<)) by Tautology.from(
      Functions.BasicTheorems.functionOnDomain of (A := initialSegment(y)(A)(<))
    )

    have(approximationUntil(f, y) |- (a ∈ initialSegment(y)(A)(<)) ==> (f(a) === F(a)(f ↾ initialSegment(a)(A)(<)))) by Restate.from(approximationUntilApp of (y := a, x := y))
    thenHave(approximationUntil(f, y) |- (a ∈ dom(f)) ==> (f(a) === F(a)(f ↾ initialSegment(a)(A)(<)))) by Substitute(`dom(f)`)
    thenHave(approximationUntil(f, y) |- ∀(a ∈ dom(f), f(a) === F(a)(f ↾ initialSegment(a)(A)(<)))) by RightForall
    thenHave(∃(y, approximationUntil(f, y)) |- ∀(a ∈ dom(f), f(a) === F(a)(f ↾ initialSegment(a)(A)(<)))) by LeftExists
    thenHave(thesis) by Restate
  }

  /**
   * Lemma --- If `f` and `g` are approximations then `dom(f) ∩ dom(g) = initialSegment(x, A, <)`
   * for some `x ∈ A`.
   */
  val approximationDomainIntersection = Lemma(
    (wellOrder(A)(<), approximation(f), approximation(g)) |- ∃(x ∈ A, dom(f) ∩ dom(g) === initialSegment(x)(A)(<))
  ) {
    assume(wellOrder(A)(<))

    val `dom(f)` = have(approximationUntil(f, x) |- dom(f) === initialSegment(x)(A)(<)) by Tautology.from(
      Functions.BasicTheorems.functionOnDomain of (A := initialSegment(x)(A)(<))
    )

    have((x ∈ A, y ∈ A) |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))) by Tautology.from(
      InitialSegment.intersectionIsInitialSegment
    )
    thenHave((x ∈ A, y ∈ A, approximationUntil(f, x), approximationUntil(g, y)) |- ∃(z ∈ A, (dom(f) ∩ dom(g)) === initialSegment(z)(A)(<))) by Substitute(
      `dom(f)`,
      `dom(f)` of (f := g, x := y)
    )
    thenHave((approximationUntil(f, x), approximationUntil(g, y)) |- ∃(z ∈ A, (dom(f) ∩ dom(g)) === initialSegment(z)(A)(<))) by Tautology
    thenHave((∃(x, approximationUntil(f, x)), approximationUntil(g, y)) |- ∃(z ∈ A, (dom(f) ∩ dom(g)) === initialSegment(z)(A)(<))) by LeftExists
    thenHave((∃(x, approximationUntil(f, x)), ∃(y, approximationUntil(g, y))) |- ∃(z ∈ A, (dom(f) ∩ dom(g)) === initialSegment(z)(A)(<))) by LeftExists
    thenHave(thesis) by Restate
  }

  /**
   * Coherence lemma --- Any two approximations of `G` agree on the
   * intersection of their domains.
   *
   * TODO: The coherence lemma could be applied to prove [[uniqueness]] by
   * relaxing the definition of approximation to include A itself. Essentially
   * the proofs of [[coherence]] and [[uniqueness]] are the same.
   */
  val coherence = Lemma(
    (wellOrder(A)(<), approximation(f), approximation(g)) |- ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))
  ) {
    assume(wellOrder(A)(<))
    assume(approximation(f))
    assume(approximation(g))

    // Unfold the definitions of f(x) and g(x) to use them later
    val `f(x)` = have(x ∈ dom(f) |- (f(x) === F(x)(f ↾ initialSegment(x)(A)(<)))) by InstantiateForall(x)(approximationApp)
    val `g(x)` = have(x ∈ dom(g) |- (g(x) === F(x)(g ↾ initialSegment(x)(A)(<)))) by InstantiateForall(x)(approximationApp of (f := g))

    // Let D = {x ∈ dom(f) ∩ dom(g) | f(x) ≠ g(x)}
    val D = { x ∈ (dom(f) ∩ dom(g)) | f(x) ≠ g(x) }
    val `x ∈ D` = have(x ∈ D <=> (x ∈ (dom(f) ∩ dom(g))) /\ (f(x) ≠ g(x))) by Comprehension.apply

    // Towards a contradiction, assume that D is non-empty.
    have(D ≠ ∅ |- ⊥) subproof {
      assume(D ≠ ∅)

      // Notice that D ⊆ A since D ⊆ dom(f) ∩ dom(g) ⊆ dom(f) ⊆ A
      val `D ⊆ A` = have(D ⊆ A) subproof {
        have(D ⊆ dom(f)) by Tautology.from(
          Comprehension.subset of (y := dom(f) ∩ dom(g), φ := λ(x, f(x) ≠ g(x))),
          Intersection.subsetLeft of (x := dom(f), y := dom(g)),
          Subset.transitivity of (x := D, y := dom(f) ∩ dom(g), z := dom(f))
        )
        thenHave(thesis) by Tautology.fromLastStep(
          approximationDomain,
          Subset.transitivity of (x := D, y := dom(f), z := A)
        )
      }

      // Hence D has a minimal element, call it x.
      // We have that f and g agree on initialSegment(x, dom(f) ∩ dom(g), <)
      have(minimal(x)(D)(<) |- (f ↾ initialSegment(x)(A)(<)) === (g ↾ initialSegment(x)(A)(<))) subproof {
        assume(minimal(x)(D)(<))

        have(∀(y ∈ D, ¬(y < x))) by Tautology.from(minimal.definition of (a := x, A := D))
        thenHave(y ∈ D ==> ¬(y < x)) by InstantiateForall(y)
        val eq = thenHave(y ∈ initialSegment(x)(dom(f) ∩ dom(g))(<) ==> (f(y) === g(y))) by Tautology.fromLastStep(
          `x ∈ D` of (x := y),
          InitialSegment.membership of (A := dom(f) ∩ dom(g))
        )

        // Since `dom(f) ∩ dom(g) = A_<a` for some `a ∈ A`
        // and `x ∈ dom(f) ∩ dom(g)` we have that `(A_<a)_<x = A_<x`
        have((z ∈ A, x ∈ initialSegment(z)(A)(<)) |- initialSegment(x)(initialSegment(z)(A)(<))(<) === initialSegment(x)(A)(<)) by Tautology.from(
          InitialSegment.absorption of (x := z, y := x)
        )
        thenHave((z ∈ A, x ∈ (dom(f) ∩ dom(g)), (dom(f) ∩ dom(g)) === initialSegment(z)(A)(<)) |- initialSegment(x)(dom(f) ∩ dom(g))(<) === initialSegment(x)(A)(<)) by Substitute(
          (dom(f) ∩ dom(g)) === initialSegment(z)(A)(<)
        )
        thenHave((x ∈ (dom(f) ∩ dom(g)), z ∈ A /\ ((dom(f) ∩ dom(g)) === initialSegment(z)(A)(<))) |- initialSegment(x)(dom(f) ∩ dom(g))(<) === initialSegment(x)(A)(<)) by Restate
        thenHave((x ∈ (dom(f) ∩ dom(g)), ∃(z ∈ A, (dom(f) ∩ dom(g)) === initialSegment(z)(A)(<))) |- initialSegment(x)(dom(f) ∩ dom(g))(<) === initialSegment(x)(A)(<)) by LeftExists
        thenHave(initialSegment(x)(dom(f) ∩ dom(g))(<) === initialSegment(x)(A)(<)) by Tautology.fromLastStep(
          minimal.definition of (a := x, A := D),
          `x ∈ D`,
          approximationDomainIntersection
        )

        have(y ∈ initialSegment(x)(A)(<) ==> (f(y) === g(y))) by Congruence.from(lastStep, eq)
        thenHave(∀(y, y ∈ initialSegment(x)(A)(<) ==> (f(y) === g(y)))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(
          Restriction.extensionality of (A := initialSegment(x)(A)(<), f := f, g := g),
          approximationIsFunction,
          approximationIsFunction of (f := g)
        )
      }

      // By definition of f(x) and g(x), this means that f(x) === g(x)
      have((x ∈ dom(f), x ∈ dom(g), minimal(x)(D)(<)) |- f(x) === g(x)) by Congruence.from(
        lastStep,
        `f(x)`,
        `g(x)`
      )

      // Contradiction since x ∈ D implies f(x) ≠ g(x)
      thenHave(minimal(x)(D)(<) |- ()) by Tautology.fromLastStep(
        minimal.definition of (a := x, A := D),
        `x ∈ D`,
        Intersection.membership of (z := x, x := dom(f), y := dom(g))
      )
      thenHave(∃(x, minimal(x)(D)(<)) |- ()) by LeftExists
      thenHave(∃(x, minimal(x)(D)(<)) |- ()) by Tautology

      // Conclude by well-foundedness
      have(thesis) by Tautology.from(
        lastStep,
        wellOrder.definition,
        WellFoundedRelation.minimalElement of (R := <, S := D, X := A),
        `D ⊆ A`
      )
    }
    // Therefore D = ∅
    thenHave(D === ∅) by Restate

    // Hence f and g agree on the intersection of their domains
    have(x ∉ D) by Congruence.from(lastStep, EmptySet.definition)
    thenHave(x ∈ (dom(f) ∩ dom(g)) ==> (f(x) === g(x))) by Tautology.fromLastStep(`x ∈ D`)
    thenHave(thesis) by RightForall
  }

  /**
   * Lemma --- Any two approximations `f` and `g` such that `dom(f) = dom(g)` are equal.
   *
   * Consequence of the [[coherence]] lemma.
   */
  val recursionStepUniqueness = Theorem(
    (
      wellOrder(A)(<),
      approximationUntil(f, x),
      approximationUntil(g, x)
    ) |- (f === g)
  ) {
    assume(wellOrder(A)(<))
    assume(approximationUntil(f, x))

    val `f is approximation` = thenHave(approximation(f)) by RightExists
    val `dom(f)` = have(dom(f) === initialSegment(x)(A)(<)) by Tautology.from(
      Functions.BasicTheorems.functionOnDomain of (A := initialSegment(x)(A)(<))
    )

    assume(approximationUntil(g, x))
    val `g is approximation` = thenHave(approximation(g)) by RightExists
    val `dom(g)` = have(dom(g) === initialSegment(x)(A)(<)) by Tautology.from(
      Functions.BasicTheorems.functionOnDomain of (f := g, A := initialSegment(x)(A)(<))
    )

    have(∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))) by Tautology.from(
      coherence,
      `f is approximation`,
      `g is approximation`
    )
    thenHave(y ∈ (dom(f) ∩ dom(g)) ==> (f(y) === g(y))) by InstantiateForall(y)

    have(y ∈ (initialSegment(x)(A)(<) ∩ initialSegment(x)(A)(<)) ==> (f(y) === g(y))) by Congruence.from(
      lastStep,
      `dom(f)`,
      `dom(g)`
    )
    thenHave(y ∈ initialSegment(x)(A)(<) ==> (f(y) === g(y))) by Substitute(Intersection.idempotence of (x := initialSegment(x)(A)(<)))
    thenHave(∀(y ∈ initialSegment(x)(A)(<), f(y) === g(y))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      Functions.BasicTheorems.extensionality of (A := initialSegment(x)(A)(<))
    )
  }

  /**
   * We say that `p` is a predecessor of `x` if `p < x` and there does not
   * exists `y` such that `p < y < x`.
   */
  def predecessor(p: Expr[Ind]): Expr[Prop] =
    (p ∈ A) /\ (p < x) /\ ¬(∃(z ∈ A, (p < z) /\ (z < x)))

  /**
   * Theorem --- If `x` has a predecessor `p` that has an approximation, then there ∃ an
   * approximation until `x`.
   */
  val successorCase = Theorem(
    (
      wellOrder(A)(<),
      x ∈ A,
      predecessor(p),
      ∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y)))
    ) |-
      ∃(G, approximationUntil(G, x))
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)

    assume(∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y))))
    thenHave((y ∈ A) ==> ((y < x) ==> ∃!(G, approximationUntil(G, y)))) by InstantiateForall(y)
    thenHave((y ∈ A, y < x) |- ∃!(G, approximationUntil(G, y))) by Restate
    val `approximationUntil(G_y, y)` = thenHave((y ∈ A, y < x) |- approximationUntil(ε(G, approximationUntil(G, y)), y)) by Tautology.fromLastStep(
      Quantifiers.existsOneEpsilon of (P := λ(G, approximationUntil(G, y)))
    )

    assume(predecessor(p))

    /**
     * We show that `G_x = G_p ∪ {(p, F(p, G_p))}` is the desired approximation.
     * This follows from the fact that `A_<x = A_<p ∪ {p}` and thus `G_x` is a
     * point extension of `G_p`.
     */
    val G_p = ε(G, approximationUntil(G, p))
    val G_x = G_p ∪ singleton((p, F(p)(G_p)))

    val initialSegmentPartition = have(initialSegment(x)(A)(<) === initialSegment(p)(A)(<) ∪ singleton(p)) by Tautology.from(InitialSegment.successor)

    val `y ∈ initialSegment(x)(A)(<)` = have(y ∈ initialSegment(x)(A)(<) <=> (y ∈ initialSegment(p)(A)(<)) \/ (y === p)) by Congruence.from(
      initialSegmentPartition,
      Union.membership of (z := y, x := initialSegment(p)(A)(<), y := singleton(p)),
      Singleton.membership of (x := p)
    )

    /**
     * 1. `G_x` is a function on `A_<x`
     */
    val `function(G_p)` = have(function(G_p)) by Tautology.from(
      `approximationUntil(G_y, y)` of (y := p),
      Functions.BasicTheorems.functionOnIsFunction of (f := G_p, A := initialSegment(p)(A)(<))
    )

    val `dom(G_p)` = have(dom(G_p) === initialSegment(p)(A)(<)) by Tautology.from(
      `approximationUntil(G_y, y)` of (y := p),
      Functions.BasicTheorems.functionOnDomain of (f := G_p, A := initialSegment(p)(A)(<))
    )

    val `G_p(y)` = have(y ∈ initialSegment(p)(A)(<) |- G_p(y) === F(y)(G_p ↾ initialSegment(y)(A)(<))) by Tautology.from(
      `approximationUntil(G_y, y)` of (y := p),
      approximationUntilApp of (f := G_p, x := p)
    )

    val `p ∉ dom(G_p)` =
      have(p ∉ initialSegment(p)(A)(<)) by Tautology.from(
        membership of (y := p, x := p),
        WellOrder.irreflexivity,
        Relations.BasicTheorems.appliedIrreflexivity of (R := <, X := A, x := p)
      )
      thenHave(p ∉ dom(G_p)) by Substitute(`dom(G_p)`)

    val `G_x is a function on A_<x` =
      have(functionOn(G_x)(dom(G_p) ∪ singleton(p))) by Tautology.from(
        Functions.BasicTheorems.pointExtension of (f := G_p, x := p, y := F(p)(G_p)),
        `function(G_p)`,
        `p ∉ dom(G_p)`
      )
      thenHave(functionOn(G_x)(initialSegment(p)(A)(<) ∪ singleton(p))) by Substitute(`dom(G_p)`)
      thenHave(functionOn(G_x)(initialSegment(x)(A)(<))) by Substitute(initialSegmentPartition)

    val `G_x is a function` = have(function(G_x)) by Tautology.from(
      `G_x is a function on A_<x`,
      Functions.BasicTheorems.functionOnIsFunction of (f := G_x, A := initialSegment(x)(A)(<))
    )

    val `dom(G_x)` = have(dom(G_x) === initialSegment(x)(A)(<)) by Tautology.from(
      `G_x is a function on A_<x`,
      Functions.BasicTheorems.functionOnDomain of (f := G_x, A := initialSegment(x)(A)(<))
    )

    val `p ∈ dom(G_x)` =
      have(p ∈ initialSegment(x)(A)(<)) by Tautology.from(InitialSegment.membership of (y := p))
      thenHave(p ∈ dom(G_x)) by Substitute(`dom(G_x)`)

    val `G_p = G_x ↾ A_<p` =
      have(G_p === (G_x ↾ dom(G_p))) by Tautology.from(
        Restriction.subsetIsRestriction of (g := G_p, f := G_x),
        Union.leftSubset of (x := G_p, y := singleton((p, F(p)(G_p)))),
        `G_x is a function`
      )
      thenHave(G_p === (G_x ↾ initialSegment(p)(A)(<))) by Substitute(`dom(G_p)`)

    /**
     * 2. For all `a ∈ A_<x` we have `G_x(a) = F(a, G_x ↾ a)`.
     * Essentially, we have to show 2 things:
     * a. For `a = p` we have `G_x(p) = F(p, G_p)` by construction, i.e. `G_x ↾ A_<p = G_p`.
     * b. For `a ∈ A_<p` we have `G_x ↾ A_<a = G_p ↾ A_<a`.
     */
    val `G_x(p)` = {
      have(G_x(p) === F(p)(G_x ↾ initialSegment(p)(A)(<))) subproof {
        have((p, F(p)(G_p)) ∈ G_x) by Tautology.from(
          Union.membership of (z := (p, F(p)(G_p)), x := G_p, y := singleton((p, F(p)(G_p)))),
          Singleton.membership of (y := (p, F(p)(G_p)), x := (p, F(p)(G_p)))
        )
        thenHave(G_x(p) === F(p)(G_p)) by Tautology.fromLastStep(
          Functions.BasicTheorems.appDefinition of (f := G_x, x := p, y := F(p)(G_p)),
          `G_x is a function`,
          `p ∈ dom(G_x)`
        )

        // Conclude
        have(thesis) by Congruence.from(lastStep, `G_p = G_x ↾ A_<p`)
      }
      thenHave(y === p |- G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<))) by Congruence
    }

    val `G_x(y)` = have(y ∈ initialSegment(p)(A)(<) |- G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<))) subproof {
      assume(y ∈ initialSegment(p)(A)(<))

      have(y ∈ initialSegment(x)(A)(<)) by Tautology.from(`y ∈ initialSegment(x)(A)(<)`)
      thenHave(y ∈ dom(G_x)) by Substitute(`dom(G_x)`)
      thenHave((G_x ↾ initialSegment(p)(A)(<))(y) === G_x(y)) by Tautology.fromLastStep(
        Restriction.restrictedApp of (f := G_x, A := initialSegment(p)(A)(<), x := y),
        `G_x is a function`
      )
      thenHave(G_p(y) === G_x(y)) by Substitute(`G_p = G_x ↾ A_<p`)
      thenHave(F(y)(G_p ↾ initialSegment(y)(A)(<)) === G_x(y)) by Substitute(`G_p(y)`)
      thenHave(F(y)((G_x ↾ initialSegment(p)(A)(<)) ↾ initialSegment(y)(A)(<)) === G_x(y)) by Substitute(`G_p = G_x ↾ A_<p`)

      // It remains to remove the redundant restriction
      thenHave(F(y)(G_x ↾ (initialSegment(p)(A)(<) ∩ initialSegment(y)(A)(<))) === G_x(y)) by Substitute(
        Restriction.doubleRestriction of (f := G_x, A := initialSegment(p)(A)(<), B := initialSegment(y)(A)(<))
      )
      thenHave(F(y)(G_x ↾ (initialSegment(y)(A)(<) ∩ initialSegment(p)(A)(<))) === G_x(y)) by Substitute(
        Intersection.commutativity of (x := initialSegment(p)(A)(<), y := initialSegment(y)(A)(<))
      )
      thenHave((y < p, y ∈ A) |- F(y)(G_x ↾ initialSegment(y)(A)(<)) === G_x(y)) by Substitute(
        InitialSegment.intersection of (x := y, y := p)
      )

      thenHave(thesis) by Tautology.fromLastStep(InitialSegment.membership of (x := p))
    }

    have(y ∈ initialSegment(x)(A)(<) ==> (G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<)))) by Tautology.from(
      `G_x(p)`,
      `G_x(y)`,
      `y ∈ initialSegment(x)(A)(<)`
    )
    thenHave(∀(y ∈ initialSegment(x)(A)(<), G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<)))) by RightForall

    /**
     * Conclude.
     */
    have(approximationUntil(G_x, x)) by Tautology.from(
      lastStep,
      `G_x is a function on A_<x`
    )
    thenHave(thesis) by RightExists
  }

  /**
   * Theorem --- If `x` is limit, then there ∃ an approximation until `x`.
   */
  val limitCase = Theorem(
    (
      wellOrder(A)(<),
      x ∈ A,
      ∀(p, ¬(predecessor(p))),
      ∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y)))
    ) |-
      ∃(G, approximationUntil(G, x))
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(∀(p, ¬(predecessor(p))))
    val `¬predecessor(y)` = thenHave(¬(predecessor(y))) by InstantiateForall(y)

    /**
     * Let `G_y` be the approximation until `y`.
     */
    def G_(y: Expr[Ind]): Expr[Ind] = ε(G, approximationUntil(G, y))

    assume(∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y))))
    thenHave((y ∈ A) ==> ((y < x) ==> ∃!(G, approximationUntil(G, y)))) by InstantiateForall(y)
    thenHave(y ∈ initialSegment(x)(A)(<) |- ∃!(G, approximationUntil(G, y))) by Tautology.fromLastStep(InitialSegment.membership)
    val `approximationUntil(G_y, y)` = thenHave(y ∈ initialSegment(x)(A)(<) |- approximationUntil(G_(y), y)) by Tautology.fromLastStep(
      Quantifiers.existsOneEpsilon of (P := λ(G, approximationUntil(G, y)))
    )
    val `approximation(G_y)` = thenHave(y ∈ initialSegment(x)(A)(<) |- approximation(G_(y))) by RightExists

    /**
     * If `x` is limit, for `G_x = ⋃{G_y | y < x}` we have that:
     * 1. `G_x` is a function since all of the approximations are coherent
     * 2. `dom(G_x) = ⋃{dom(G_y) | y < x} = A_<x`
     * 3. For any `y < x` we have `G_x ↾ A_<y = G_y`.
     */
    val S = { G_(y) | y ∈ initialSegment(x)(A)(<) }
    val G_x = ⋃(S)

    val replacement_F = Variable[Ind >>: Ind]("F") // Unfortunate name clash with F : Set -> Set -> Set
    val `G_y ∈ S` = have(y ∈ initialSegment(x)(A)(<) |- G_(y) ∈ S) by Tautology.from(
      Replacement.map of (A := initialSegment(x)(A)(<), x := y, replacement_F := λ(y, G_(y)))
    )

    val `G_y ⊆ G_x` = have(y ∈ initialSegment(x)(A)(<) |- G_(y) ⊆ G_x) by Tautology.from(
      `G_y ∈ S`,
      Union.subset of (y := G_(y), x := S)
    )

    /**
     * 1. `G_x` is a function
     */
    val `f ∈ S` = have(f ∈ S <=> ∃(y ∈ initialSegment(x)(A)(<), G_(y) === f)) by Replacement.apply

    val `G_y is a function` = have(y ∈ initialSegment(x)(A)(<) |- function(G_(y))) by Tautology.from(
      `approximationUntil(G_y, y)`,
      Functions.BasicTheorems.functionOnIsFunction of (f := G_(y), A := initialSegment(y)(A)(<))
    )

    val `dom(G_y)` = have(y ∈ initialSegment(x)(A)(<) |- dom(G_(y)) === initialSegment(y)(A)(<)) by Tautology.from(
      `approximationUntil(G_y, y)`,
      Functions.BasicTheorems.functionOnDomain of (f := G_(y), A := initialSegment(y)(A)(<))
    )

    val `f ∈ S is a function` = {
      have((y ∈ initialSegment(x)(A)(<), f === G_(y)) |- function(f)) by Congruence.from(`G_y is a function`)
      thenHave((y ∈ initialSegment(x)(A)(<)) /\ (f === G_(y)) |- function(f)) by Restate
      thenHave(∃(y ∈ initialSegment(x)(A)(<), f === G_(y)) |- function(f)) by LeftExists
      thenHave(f ∈ S |- function(f)) by Substitute(`f ∈ S`)
      thenHave(f ∈ S ==> function(f)) by Restate
      thenHave(∀(f, f ∈ S ==> function(f))) by RightForall
    }

    val `f, g ∈ S are coherent` = {
      have((y ∈ initialSegment(x)(A)(<), z ∈ initialSegment(x)(A)(<)) |- approximation(G_(y)) /\ approximation(G_(z))) by Tautology.from(
        `approximation(G_y)`,
        `approximation(G_y)` of (y := z)
      )
      thenHave(
        (
          y ∈ initialSegment(x)(A)(<),
          f === G_(y),
          z ∈ initialSegment(x)(A)(<),
          g === G_(z)
        ) |- approximation(f) /\ approximation(g)
      ) by Substitute(f === G_(y), g === G_(z))
      thenHave(
        (
          (y ∈ initialSegment(x)(A)(<)) /\ (f === G_(y)),
          (z ∈ initialSegment(x)(A)(<)) /\ (g === G_(z))
        ) |- ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))
      ) by Tautology.fromLastStep(coherence)
      thenHave(
        (
          ∃(y ∈ initialSegment(x)(A)(<), f === G_(y)),
          (z ∈ initialSegment(x)(A)(<)) /\ (g === G_(z))
        ) |- ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))
      ) by LeftExists
      thenHave(
        (
          ∃(y ∈ initialSegment(x)(A)(<), f === G_(y)),
          ∃(z ∈ initialSegment(x)(A)(<), g === G_(z))
        ) |- ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))
      ) by LeftExists
      thenHave((f ∈ S, g ∈ S) |- ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))) by Substitute(
        `f ∈ S`,
        `f ∈ S` of (f := g)
      )
      thenHave(f ∈ S |- (g ∈ S) ==> ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))) by Restate
      thenHave(f ∈ S |- ∀(g ∈ S, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x)))) by RightForall
      thenHave(f ∈ S ==> ∀(g ∈ S, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x)))) by Restate
      thenHave(∀(f ∈ S, ∀(g ∈ S, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))))) by RightForall
    }

    val `G_x is a function` = have(function(G_x)) by Tautology.from(
      Functions.Operations.Union.isFunction of (𝓕 := S),
      `f ∈ S is a function`,
      `f, g ∈ S are coherent`
    )

    /**
     * 2. `dom(G_x) = A_<x`
     */
    val `dom(G_x)` = have(dom(G_x) === initialSegment(x)(A)(<)) subproof {

      /**
       * We proceed by double inclusion: we have both
       * 1. dom(G_x) ⊆ A_<x, for dom(G_y) ⊆ A_<x for every y ∈ A_<x
       * 2. A_<x ⊆ dom(G_x), since for every y ∈ A_<x there ∃ z > y such that y ∈ dom(G_z)
       */

      val D = { dom(f) | f ∈ S }
      val `d ∈ D` = have(d ∈ D <=> ∃(f ∈ S, dom(f) === d)) by Replacement.apply

      val `dom(G_y) ∈ D` =
        have(y ∈ initialSegment(x)(A)(<) |- (G_(y) ∈ S) /\ (dom(G_(y)) === dom(G_(y)))) by Tautology.from(`G_y ∈ S`)
        thenHave(y ∈ initialSegment(x)(A)(<) |- ∃(f ∈ S, dom(f) === dom(G_(y)))) by RightExists
        thenHave(y ∈ initialSegment(x)(A)(<) |- dom(G_(y)) ∈ D) by Substitute(`d ∈ D` of (d := dom(G_(y))))

      val `==>` = have(⋃(D) ⊆ initialSegment(x)(A)(<)) subproof {
        have((y ∈ initialSegment(x)(A)(<), y ∈ A, y < x, G_(y) === f, dom(f) === d) |- d ⊆ initialSegment(x)(A)(<)) by Congruence.from(
          InitialSegment.monotonic of (x := y, y := x),
          `dom(G_y)`
        )
        thenHave(((y ∈ initialSegment(x)(A)(<)) /\ (G_(y) === f), dom(f) === d) |- d ⊆ initialSegment(x)(A)(<)) by Tautology.fromLastStep(
          InitialSegment.membership
        )
        thenHave((∃(y ∈ initialSegment(x)(A)(<), G_(y) === f), dom(f) === d) |- d ⊆ initialSegment(x)(A)(<)) by LeftExists
        thenHave((f ∈ S, dom(f) === d) |- d ⊆ initialSegment(x)(A)(<)) by Substitute(`f ∈ S`)
        thenHave((f ∈ S) /\ (dom(f) === d) |- d ⊆ initialSegment(x)(A)(<)) by Restate
        thenHave(∃(f ∈ S, dom(f) === d) |- d ⊆ initialSegment(x)(A)(<)) by LeftExists
        thenHave(d ∈ D |- d ⊆ initialSegment(x)(A)(<)) by Substitute(`d ∈ D`)
        thenHave(d ∈ D ==> (d ⊆ initialSegment(x)(A)(<))) by Restate
        thenHave(∀(d ∈ D, d ⊆ initialSegment(x)(A)(<))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(Union.leftUnaryUnionSubset of (z := initialSegment(x)(A)(<), x := D))
      }

      val `<==` = have(initialSegment(x)(A)(<) ⊆ ⋃(D)) subproof {

        /**
         * Since `y` is limit, `y ∈ dom(G_z)` for any `z > y`.
         */
        have((y ∈ initialSegment(x)(A)(<), z ∈ initialSegment(x)(A)(<), y < z) |- y ∈ initialSegment(z)(A)(<)) by Tautology.from(
          InitialSegment.membership,
          InitialSegment.membership of (x := z),
          InitialSegment.membership of (y := z)
        )
        thenHave((y ∈ initialSegment(x)(A)(<), z ∈ initialSegment(x)(A)(<), y < z) |- y ∈ dom(G_(z))) by Substitute(`dom(G_y)` of (y := z))
        thenHave((y ∈ initialSegment(x)(A)(<), z ∈ initialSegment(x)(A)(<), y < z) |- (dom(G_(z)) ∈ D) /\ y ∈ dom(G_(z))) by Tautology.fromLastStep(`dom(G_y) ∈ D` of (y := z))
        thenHave((y ∈ initialSegment(x)(A)(<), z ∈ initialSegment(x)(A)(<), y < z) |- ∃(d ∈ D, y ∈ d)) by RightExists
        thenHave((y ∈ initialSegment(x)(A)(<), z ∈ initialSegment(x)(A)(<), y < z) |- y ∈ ⋃(D)) by Substitute(⋃.definition of (z := y, x := D))
        thenHave((z ∈ A) /\ (y < z) /\ (z < x) |- y ∈ initialSegment(x)(A)(<) ==> (y ∈ ⋃(D))) by Tautology.fromLastStep(
          InitialSegment.membership of (y := z)
        )
        thenHave(∃(z ∈ A, (y < z) /\ (z < x)) |- y ∈ initialSegment(x)(A)(<) ==> (y ∈ ⋃(D))) by LeftExists
        thenHave(y ∈ initialSegment(x)(A)(<) ==> (y ∈ ⋃(D))) by Tautology.fromLastStep(
          `¬predecessor(y)`,
          InitialSegment.membership
        )
        thenHave(∀(y, y ∈ initialSegment(x)(A)(<) ==> (y ∈ ⋃(D)))) by RightForall
        thenHave(thesis) by Substitute(⊆.definition of (x := initialSegment(x)(A)(<), y := ⋃(D)))
      }

      have(⋃(D) === initialSegment(x)(A)(<)) by Tautology.from(
        `==>`,
        `<==`,
        Subset.doubleInclusion of (x := ⋃(D), y := initialSegment(x)(A)(<))
      )
      thenHave(thesis) by Substitute(Functions.Operations.Union.domain of (𝓕 := S))
    }

    /**
     * 3. For all `y < x` we have `G_x(y) = F(y, G_x ↾ A_<y)`.
     *
     * Since `x` is limit, there exists an element `y < z < x` such that
     * `G_x(y) = G_z(y)`, and by construction
     *
     *   `G_z(y) = F(y, G_z ↾ A_<y) = F(y, G_x ↾ A_<y)`
     *
     * as desired.
     */
    val `G_y = G_x ↾ A_<y` =
      have(y ∈ initialSegment(x)(A)(<) |- G_(y) === (G_x ↾ dom(G_(y)))) by Tautology.from(
        Restriction.subsetIsRestriction of (f := G_x, g := G_(y)),
        `G_x is a function`,
        `G_y ⊆ G_x`
      )
      thenHave(y ∈ initialSegment(x)(A)(<) |- G_(y) === (G_x ↾ initialSegment(y)(A)(<))) by Substitute(`dom(G_y)`)

    have(y ∈ initialSegment(x)(A)(<) |- G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<))) subproof {
      assume(y ∈ initialSegment(x)(A)(<))

      val `y ∈ dom(G_z)` = have((z ∈ initialSegment(x)(A)(<), y ∈ initialSegment(z)(A)(<)) |- y ∈ dom(G_(z))) by Congruence.from(`dom(G_y)` of (y := z))

      /**
       * We show that if `y < z` then `G_z(y) = F(y, G_x ↾ A_<y)`.
       */
      have((y ∈ initialSegment(z)(A)(<), z ∈ initialSegment(x)(A)(<)) |- G_(z)(y) === F(y)(G_x ↾ initialSegment(y)(A)(<))) subproof {
        assume(y ∈ initialSegment(z)(A)(<))
        assume(z ∈ initialSegment(x)(A)(<))

        have(G_(z)(y) === F(y)(G_(z) ↾ initialSegment(y)(A)(<))) by Tautology.from(
          approximationUntilApp of (f := G_(z), x := z),
          `approximationUntil(G_y, y)` of (y := z)
        )
        thenHave(G_(z)(y) === F(y)((G_x ↾ initialSegment(z)(A)(<)) ↾ initialSegment(y)(A)(<))) by Substitute(
          `G_y = G_x ↾ A_<y` of (y := z)
        )
        thenHave(G_(z)(y) === F(y)(G_x ↾ (initialSegment(z)(A)(<) ∩ initialSegment(y)(A)(<)))) by Substitute(
          Restriction.doubleRestriction of (f := G_x, A := initialSegment(z)(A)(<), B := initialSegment(y)(A)(<))
        )
        thenHave(G_(z)(y) === F(y)(G_x ↾ (initialSegment(y)(A)(<) ∩ initialSegment(z)(A)(<)))) by Substitute(
          Intersection.commutativity of (x := initialSegment(y)(A)(<), y := initialSegment(z)(A)(<))
        )
        thenHave((y < z, y ∈ A, z ∈ A) |- G_(z)(y) === F(y)(G_x ↾ initialSegment(y)(A)(<))) by Substitute(
          InitialSegment.intersection of (x := y, y := z)
        )
        thenHave(thesis) by Tautology.fromLastStep(
          InitialSegment.membership of (x := z),
          InitialSegment.membership of (y := z)
        )
      }

      /**
       * Since `G_z ⊆ G_x` we have `G_x(y) = G_z(y) = F(y, G_x ↾ A_<y)` as desired.
       */
      have((y ∈ initialSegment(z)(A)(<), z ∈ initialSegment(x)(A)(<)) |- (G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<)))) by Tautology.from(
        lastStep,
        Functions.BasicTheorems.extensionApp of (f := G_x, g := G_(z), x := y, y := F(y)(G_x ↾ initialSegment(y)(A)(<))),
        `G_x is a function`,
        `G_y is a function` of (y := z),
        `G_y ⊆ G_x` of (y := z),
        `y ∈ dom(G_z)`
      )

      /**
       * Infer the existence of `z` since `x` is limit.
       */
      thenHave((y ∈ A, (z ∈ A) /\ (y < z) /\ (z < x)) |- (G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<)))) by Tautology.fromLastStep(
        InitialSegment.membership of (x := z),
        InitialSegment.membership of (y := z)
      )
      thenHave((y ∈ A, ∃(z ∈ A, (y < z) /\ (z < x))) |- (G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<)))) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(
        `¬predecessor(y)`,
        InitialSegment.membership
      )
    }
    thenHave(y ∈ initialSegment(x)(A)(<) ==> (G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<)))) by Restate
    thenHave(∀(y ∈ initialSegment(x)(A)(<), G_x(y) === F(y)(G_x ↾ initialSegment(y)(A)(<)))) by RightForall

    have(approximationUntil(G_x, x)) by Tautology.from(
      lastStep,
      Functions.BasicTheorems.functionOnIffFunctionWithDomain of (f := G_x, A := initialSegment(x)(A)(<)),
      `G_x is a function`,
      `dom(G_x)`
    )
    thenHave(thesis) by RightExists
  }

  /**
   * Theorem --- Assuming that there ∃ a unique approximation `G_y` for all `y < x`, construct
   * an approximation `G_x` with `dom(G_x) = initialSegment(x, A, <)`.
   */
  val recursionStepExistence = Theorem(
    (
      wellOrder(A)(<),
      x ∈ A,
      ∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y)))
    ) |-
      ∃(G, approximationUntil(G, x))
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y))))

    val `x has a predecessor` = have(∃(p, predecessor(p)) |- ∃(G, approximationUntil(G, x))) by LeftExists(successorCase)
    val `x is limit` = limitCase

    have(thesis) by Tautology.from(`x has a predecessor`, `x is limit`)
  }

  /**
   * Theorem --- Assuming that there ∃ a unique approximation `G_y` for all `y < x`, there ∃
   * a unique approximation `G_x` with `dom(G_x) = initialSegment(x, A, <)`.
   *
   * Combines [[recursionStepExistence]] with [[recursionStepUniqueness]].
   */
  val recursionStep = Theorem(
    (
      wellOrder(A)(<),
      x ∈ A,
      ∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y)))
    ) |-
      ∃!(G, approximationUntil(G, x))
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y))))

    val existence = have(∃(G, approximationUntil(G, x))) by Tautology.from(recursionStepExistence)

    val uniqueness =
      have(approximationUntil(f, x) /\ approximationUntil(g, x) ==> (f === g)) by Tautology.from(recursionStepUniqueness)
      thenHave(∀(f, ∀(g, approximationUntil(f, x) /\ approximationUntil(g, x) ==> (f === g)))) by Generalize

    have(thesis) by Tautology.from(
      existence,
      uniqueness,
      Quantifiers.existsOneAlternativeDefinition of (P := λ(f, approximationUntil(f, x)))
    )
  }

  /**
   * Theorem --- For any `x ∈ A` there ∃ an approximation on `A_<x`.
   *
   * This theorem justifies the construction of sequences of ordinals up to an
   * ordinal `α`, since `(α, ∈_α)` is a well-order.
   */
  val recursiveSequence = Theorem(
    wellOrder(A)(<) |- ∀(x ∈ A, ∃!(G, approximationUntil(G, x)))
  ) {
    assume(wellOrder(A)(<))

    // Apply [[WellOrderedInduction.induction]] on [[recursionStep]].
    have(x ∈ A ==> (∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y))) ==> ∃!(G, approximationUntil(G, x)))) by Restate.from(recursionStep)
    thenHave(∀(x ∈ A, ∀(y ∈ A, (y < x) ==> ∃!(G, approximationUntil(G, y))) ==> ∃!(G, approximationUntil(G, x)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      WellOrderedInduction.induction of (P := λ(x, ∃!(G, approximationUntil(G, x))))
    )
  }

  /**
   * Well-ordered recursion --- Given `F : V × V -> V` and a well-order `(A, <)`
   * there exists a function `G : A -> V` such that
   *
   *   `∀x ∈ A. G(x) = F(x, G↾A_<x)`
   *
   * This recursion principle implies recursion on any ordinal `α`, since `α`
   * is well-ordered by the membership relation, and `α_<β = β` for `β ∈ α`.
   */
  val existence = Theorem(
    wellOrder(A)(<) |- ∃(G, ∀(x ∈ A, G(x) === F(x)(G ↾ initialSegment(x)(A)(<))))
  ) {
    assume(wellOrder(A)(<))

    /**
     * We use [[recursiveSequence]] on the successor well-order `(A ∪ {m}, < ∪
     * {(x, m) | x ∈ A})` where `m` is a fresh element. Hence we obtain a
     * function that is defined for all `x < m`, i.e. for all `x ∈ A`.
     *
     * This also means that this theorem isn't necessary per se (and
     * [[recursiveSequence]] is enough), since this successor trick always
     * works.
     */

    sorry
  }

  /**
   * Definition --- `recursiveFunction(F, A, <)` builds the function obtained by well-ordered
   * recursion of `F` on `(A, <)`.
   */
  val recursiveFunction = DEF(λ(F, λ(A, λ(<, ε(G, ∀(x ∈ A, G(x) === F(x)(G ↾ initialSegment(x)(A)(<))))))))

}
