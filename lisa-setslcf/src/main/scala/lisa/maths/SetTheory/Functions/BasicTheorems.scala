package lisa.maths.SetTheory.Functions

import lisa.maths.Quantifiers
import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef._

import Function._
import Pi._

/**
 * This file contains proofs of basic properties about functions.
 *
 * TODO: Add constant functions
 * TODO: Add Cantor's theorem (probably in a distinct file, when we get to cardinals).
 */
object BasicTheorems extends lisa.Main {

  private val e1, e2 = variable[Ind]
  private val S = variable[Ind]
  private val T, T1 = variable[Ind]
  private val t, u = variable[Ind >>: Ind]
  private val T2 = variable[Ind >>: Ind]
  private val P, Q = variable[Ind >>: Prop]
  // Function
  private val e = variable[Ind >>: Ind]
  // Set functions
  private val Gf, Hf = variable[Ind >>: Ind]

  extension (f: Expr[Ind]) {

    /**
     * Syntax for `f(x)`.
     */
    def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  ////////////////////////////////////////////////////////////////////////////
  section("Membership")

  /**
   * Theorem --- If `f` is a function and `z ∈ f` then `z` is a pair.
   */
  val inversion = Theorem(
    (function(f), z ∈ f) |- (z === (fst(z), snd(z)))
  ) {
    assume(z ∈ f)
    have(functionBetween(f)(A)(B) |- (z === (fst(z), snd(z)))) by Tautology.from(
      functionBetween.definition,
      Relations.BasicTheorems.relationBetweenIsRelation of (R := f, X := A, Y := B),
      Relations.BasicTheorems.inversion of (R := f)
    )
    thenHave(∃(B, functionBetween(f)(A)(B)) |- (z === (fst(z), snd(z)))) by LeftExists
    thenHave(∃(A, ∃(B, functionBetween(f)(A)(B))) |- (z === (fst(z), snd(z)))) by LeftExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Theorem --- If `(x, y) ∈ f` then `x ∈ dom(f)`.
   *
   * Equivalent to [[Relations.BasicTheorems.domainMembership]].
   */
  val domainMembership = Theorem(
    (x, y) ∈ f |- x ∈ dom(f)
  ) {
    have(thesis) by Restate.from(Relations.BasicTheorems.domainMembership of (R := f))
  }

  /**
   * Theorem --- If `g ⊆ f` then `dom(g) ⊆ dom(f)`.
   */
  val domainMonotonic = Theorem(
    g ⊆ f |- dom(g) ⊆ dom(f)
  ) {
    have(x ∈ { fst(z) | z ∈ g } <=> ∃(z ∈ g, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(g)` = thenHave(x ∈ dom(g) <=> ∃(z ∈ g, fst(z) === x)) by Substitute(dom.definition of (R := g))
    thenHave((∀(z, z ∈ g ==> (z ∈ f)), x ∈ dom(g)) |- ∃(z ∈ f, fst(z) === x)) by Tableau
    thenHave((g ⊆ f, x ∈ dom(g)) |- x ∈ dom(f)) by Substitute(
      ⊆.definition of (x := g, y := f),
      `x ∈ dom(g)` of (g := f)
    )
    thenHave(g ⊆ f |- x ∈ dom(g) ==> (x ∈ dom(f))) by Restate
    thenHave(g ⊆ f |- ∀(x, x ∈ dom(g) ==> (x ∈ dom(f)))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := dom(g), y := dom(f)))
  }

  /**
   * Theorem --- If `(x, y) ∈ f` then `y ∈ range(f)`.
   *
   * Equivalent to [[Relations.BasicTheorems.rangeMembership]].
   */
  val rangeMembership = Theorem(
    (x, y) ∈ f |- y ∈ range(f)
  ) {
    have(thesis) by Restate.from(Relations.BasicTheorems.rangeMembership of (R := f))
  }

  /**
   * Theorem --- If `g ⊆ f` then `range(g) ⊆ range(f)`.
   */
  val rangeMonotonic = Theorem(
    g ⊆ f |- range(g) ⊆ range(f)
  ) {
    have(y ∈ { snd(z) | z ∈ g } <=> ∃(z ∈ g, snd(z) === y)) by Replacement.apply
    val `y ∈ range(g)` = thenHave(y ∈ range(g) <=> ∃(z ∈ g, snd(z) === y)) by Substitute(range.definition of (R := g))
    thenHave((∀(z, z ∈ g ==> (z ∈ f)), y ∈ range(g)) |- ∃(z ∈ f, snd(z) === y)) by Tableau
    thenHave((g ⊆ f, y ∈ range(g)) |- y ∈ range(f)) by Substitute(
      ⊆.definition of (y := g, y := f),
      `y ∈ range(g)` of (g := f)
    )
    thenHave(g ⊆ f |- y ∈ range(g) ==> (y ∈ range(f))) by Restate
    thenHave(g ⊆ f |- ∀(y, y ∈ range(g) ==> (y ∈ range(f)))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (y := range(g), y := range(f)))
  }

  /////////////////////////////////////////////////////////////////////////
  section("Functions from A to B")

  /**
   * Lemma --- If `f : A -> B` then `f` is a function.
   */
  val functionBetweenIsFunction = Theorem(
    functionBetween(f)(A)(B) |- function(f)
  ) {
    assume(functionBetween(f)(A)(B))
    thenHave(∃(B, functionBetween(f)(A)(B))) by RightExists
    thenHave(∃(A, ∃(B, functionBetween(f)(A)(B)))) by RightExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Lemma --- If `f : A -> B` then `f` is a function on `A`.
   */
  val functionBetweenIsFunctionOn = Theorem(
    functionBetween(f)(A)(B) |- functionOn(f)(A)
  ) {
    assume(functionBetween(f)(A)(B))
    thenHave(∃(B, functionBetween(f)(A)(B))) by RightExists
    thenHave(thesis) by Substitute(functionOn.definition)
  }

  /**
   * Theorem --- If `f : A -> B` then `dom(f) = A`.
   */
  val functionBetweenDomain = Theorem(
    functionBetween(f)(A)(B) |- dom(f) === A
  ) {
    assume(functionBetween(f)(A)(B))

    have(x ∈ { fst(z) | z ∈ f } <=> ∃(z ∈ f, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(f)` = thenHave(x ∈ dom(f) <=> ∃(z ∈ f, fst(z) === x)) by Substitute(dom.definition)

    // We show that `A ⊆ dom(f)`; the other direction is guaranteed by [[relationBetweenDomain]].
    have(A ⊆ dom(f)) subproof {
      have(∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
      thenHave(x ∈ A |- ∃!(y, (x, y) ∈ f)) by InstantiateForall(x)
      val existence = thenHave(x ∈ A |- ∃(y, (x, y) ∈ f)) by Tautology.fromLastStep(
        Quantifiers.existsOneImpliesExists of (P := λ(y, (x, y) ∈ f))
      )

      have((x, y) ∈ f |- x ∈ dom(f)) by Tautology.from(Relations.BasicTheorems.domainMembership of (R := f))
      thenHave(∃(y, (x, y) ∈ f) |- x ∈ dom(f)) by LeftExists

      have(x ∈ A ==> x ∈ dom(f)) by Tautology.from(
        lastStep,
        existence,
        `x ∈ dom(f)`
      )
      thenHave(∀(x, x ∈ A ==> x ∈ dom(f))) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := A, y := dom(f)))
    }
    thenHave(thesis) by Tautology.fromLastStep(
      functionBetween.definition,
      Relations.BasicTheorems.relationBetweenDomain of (R := f, X := A, Y := B),
      Subset.doubleInclusion of (x := A, y := dom(f))
    )
  }

  /**
   * Theorem --- If `f : A -> B` then `range(f) ⊆ B`.
   *
   * Consequence of [[relationBetweenRange]].
   */
  val functionBetweenRange = Theorem(
    functionBetween(f)(A)(B) |- range(f) ⊆ B
  ) {
    have(thesis) by Tautology.from(
      functionBetween.definition,
      Relations.BasicTheorems.relationBetweenRange of (R := f, X := A, Y := B)
    )
  }

  ////////////////////////////////////////////////////////////////////////////
  section("Function application")

  /**
   * Theorem --- If `f` is a function then `f(x) = y` if and only if `(x, y) ∈ f`.
   */
  val appDefinition = Theorem(
    (function(f), x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f
  ) {
    have(functionBetween(f)(A)(B) |- ∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
    thenHave((functionBetween(f)(A)(B), x ∈ A) |- ∃!(y, (x, y) ∈ f)) by InstantiateForall(x)
    thenHave((functionBetween(f)(A)(B), x ∈ A) |- (ε(y, (x, y) ∈ f) === y) <=> (x, y) ∈ f) by Tautology.fromLastStep(
      Quantifiers.existsOneEpsilonUniqueness of (P := λ(y, (x, y) ∈ f))
    )
    thenHave((functionBetween(f)(A)(B), x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f) by Substitute(
      app.definition,
      functionBetweenDomain
    )
    thenHave((∃(B, functionBetween(f)(A)(B)), x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f) by LeftExists
    thenHave((∃(A, ∃(B, functionBetween(f)(A)(B))), x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f) by LeftExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Theorem --- If `f` is a function and `x ∈ dom(f)` then `f(x) ∈ range(f)`.
   */
  val appInRange = Theorem(
    (function(f), x ∈ dom(f)) |- f(x) ∈ range(f)
  ) {
    assume(function(f))
    assume(x ∈ dom(f))

    have((x, f(x)) ∈ f) by Tautology.from(appDefinition of (y := f(x)))
    thenHave(thesis) by Tautology.fromLastStep(
      Relations.BasicTheorems.rangeMembership of (R := f, y := f(x))
    )
  }

  /**
   * Theorem --- If `f : A -> B` and `x ∈ A` then `f(x) ∈ B`.
   *
   * Special case of [[appInRange]].
   */
  val appTyping = Theorem(
    (functionBetween(f)(A)(B), x ∈ A) |- (f(x) ∈ B)
  ) {
    assume(functionBetween(f)(A)(B))
    assume(x ∈ A)
    have(x ∈ dom(f)) by Congruence.from(functionBetweenDomain)
    thenHave(f(x) ∈ range(f)) by Tautology.fromLastStep(
      functionBetweenIsFunction,
      appInRange
    )
    thenHave(thesis) by Tautology.fromLastStep(
      functionBetweenRange,
      Subset.membership of (x := range(f), y := B, z := f(x))
    )
  }

  ////////////////////////////////////////////////////////////////////////
  section("Functions on A")

  /**
   * Lemma --- If `f` is a function on `A` then `f` is a function.
   */
  val functionOnIsFunction = Theorem(
    functionOn(f)(A) |- function(f)
  ) {
    assume(functionOn(f)(A))
    thenHave(∃(B, functionBetween(f)(A)(B))) by Substitute(functionOn.definition)
    thenHave(∃(A, ∃(B, functionBetween(f)(A)(B)))) by RightExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Theorem --- If `f` is a function on `A` then `dom(f) = A`.
   *
   * Consequence of [[functionBetweenDomain]].
   */
  val functionOnDomain = Theorem(
    functionOn(f)(A) |- dom(f) === A
  ) {
    have(∃(B, functionBetween(f)(A)(B)) |- dom(f) === A) by LeftExists(functionBetweenDomain)
    thenHave(thesis) by Substitute(functionOn.definition)
  }

  /**
   * Theorem --- `f` is a function on `A` <=> `f` is a function with `dom(f) = A`.
   */
  val functionOnIffFunctionWithDomain = Theorem(
    functionOn(f)(A) <=> function(f) /\ (dom(f) === A)
  ) {
    val `==>` = have(functionOn(f)(A) |- function(f) /\ (dom(f) === A)) by RightAnd(functionOnIsFunction, functionOnDomain)

    val `<==` =
      have((functionBetween(f)(C)(D), dom(f) === A) |- dom(f) === C) by Tautology.from(functionBetweenDomain of (A := C, B := D))
      thenHave((functionBetween(f)(C)(D), dom(f) === A) |- (functionBetween(f)(A)(D))) by Congruence
      thenHave((functionBetween(f)(C)(D), dom(f) === A) |- ∃(B, functionBetween(f)(A)(B))) by RightExists
      thenHave((functionBetween(f)(C)(D), dom(f) === A) |- functionOn(f)(A)) by Substitute(functionOn.definition)
      thenHave((∃(D, functionBetween(f)(C)(D)), dom(f) === A) |- functionOn(f)(A)) by LeftExists
      thenHave((∃(C, ∃(D, functionBetween(f)(C)(D))), dom(f) === A) |- functionOn(f)(A)) by LeftExists
      thenHave((function(f), dom(f) === A) |- functionOn(f)(A)) by Substitute(function.definition)

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Theorem --- If `f` and `g` are functions on `A` such that `f(x) = g(x)`
   * for all `x ∈ A`, then `f` equals `g`.
   */
  val extensionality = Theorem(
    (
      functionOn(f)(A),
      functionOn(g)(A),
      ∀(x ∈ A, f(x) === g(x))
    ) |- (f === g)
  ) {
    assume(functionOn(f)(A))
    assume(functionOn(g)(A))
    assume(∀(x ∈ A, f(x) === g(x)))

    thenHave(x ∈ A |- f(x) === g(x)) by InstantiateForall(x)
    val `f(x)` = thenHave(x ∈ dom(f) |- f(x) === g(x)) by Substitute(functionOnDomain)

    // Take z ∈ f. We show that z ∈ g.
    val `==>` = have(z ∈ f |- z ∈ g) subproof {
      assume(z ∈ f)

      // 1. z = (fst(z), snd(z))
      val step1 = have(z === (fst(z), snd(z))) by Tautology.from(inversion, functionOnIsFunction)

      // 2. (fst(z), snd(z)) ∈ f
      val step2 = thenHave((fst(z), snd(z)) ∈ f) by Congruence

      // 3. fst(z) ∈ dom(f)
      val step3 = thenHave(fst(z) ∈ dom(f)) by Tautology.fromLastStep(domainMembership of (x := fst(z), y := snd(z)))

      // 4. f(fst(z)) = snd(z)
      val step4 = have(f(fst(z)) === snd(z)) by Tautology.from(
        appDefinition of (x := fst(z), y := snd(z)),
        functionOnIsFunction,
        step3,
        step2
      )

      // 5. f(fst(z)) = g(fst(z))
      val step5 = have(f(fst(z)) === g(fst(z))) by Tautology.from(
        `f(x)` of (x := fst(z)),
        step3
      )

      // 6. g(fst(z)) = snd(z)
      val step6 = have(g(fst(z)) === snd(z)) by Congruence.from(
        step5,
        step4
      )

      // 7. fst(z) ∈ dom(g)
      val step7 = have(fst(z) ∈ dom(g)) by Congruence.from(
        step3,
        functionOnDomain of (f := f),
        functionOnDomain of (f := g)
      )

      // 8. (fst(z), snd(z)) ∈ g
      val step8 = have((fst(z), snd(z)) ∈ g) by Congruence.from(
        appDefinition of (f := g, x := fst(z), y := snd(z)),
        functionOnIsFunction of (f := g),
        step7,
        step6
      )

      // 9. z ∈ g
      thenHave(thesis) by Substitute(step1)
    }

    /**
     * The reverse implication is obtained by symmetry.
     */
    val `<==` = have(z ∈ g |- z ∈ f) by Tautology.from(`==>` of (f := g, g := f))

    have(z ∈ f <=> z ∈ g) by Tautology.from(`==>`, `<==`)
    thenHave(thesis) by Extensionality
  }

  /////////////////////////////////////////////////////////////////////////
  section("Subsets, extensions")

  /**
   * Lemma --- If `f` is a function then `f` is a relation.
   */
  val functionIsRelation = Theorem(
    function(f) |- relation(f)
  ) {
    have(functionBetween(f)(A)(B) |- relation(f)) by Tautology.from(
      functionBetween.definition,
      Relations.BasicTheorems.relationBetweenIsRelation of (R := f, X := A, Y := B)
    )
    thenHave(∃(B, functionBetween(f)(A)(B)) |- relation(f)) by LeftExists
    thenHave(∃(A, ∃(B, functionBetween(f)(A)(B))) |- relation(f)) by LeftExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Lemma --- If `f` is a function then `f ⊆ dom(f) × range(f)`.
   */
  val functionBetweenDomainRange = Theorem(
    function(f) |- relationBetween(f)(dom(f))(range(f))
  ) {
    have(thesis) by Tautology.from(
      functionIsRelation,
      Relations.BasicTheorems.relationBetweenDomainRange of (R := f)
    )
  }

  /**
   * Lemma --- If `f` is a function and `x ∈ dom(f)`, then there is a unique `y` such that `(x, y) ∈ f`.
   */
  val functionUniqueAtDomain = Theorem(
    (function(f), x ∈ dom(f)) |- ∃!(y, (x, y) ∈ f)
  ) {
    val local = have((functionBetween(f)(A)(B), x ∈ dom(f)) |- ∃!(y, (x, y) ∈ f)) subproof {
      assume(functionBetween(f)(A)(B))
      assume(x ∈ dom(f))

      val dom_eq = have(dom(f) === A) by Tautology.from(functionBetweenDomain)
      val x_in_dom = have(x ∈ dom(f)) by Hypothesis
      val x_in_A = have(x ∈ A) by Congruence.from(x_in_dom, dom_eq)

      have(∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
      thenHave(x ∈ A |- ∃!(y, (x, y) ∈ f)) by InstantiateForall(x)
      have(thesis) by Cut(x_in_A, lastStep)
    }

    have((∃(B, functionBetween(f)(A)(B)), x ∈ dom(f)) |- ∃!(y, (x, y) ∈ f)) by LeftExists(local)
    thenHave((∃(A, ∃(B, functionBetween(f)(A)(B))), x ∈ dom(f)) |- ∃!(y, (x, y) ∈ f)) by LeftExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Theorem --- If `f` is a function and `g ⊆ f` then `g` is also a function.
   */
  val subset = Theorem(
    (function(f), g ⊆ f) |- function(g)
  ) {
    assume(function(f))
    assume(g ⊆ f)

    // First, we show that `g` is a relation
    val `g is relation between dom(g) and range(g)` = have(functionBetween(f)(A)(B) |- relationBetween(g)(dom(g))(range(g))) subproof {
      assume(functionBetween(f)(A)(B))
      have(relationBetween(f)(A)(B)) by Tautology.from(functionBetween.definition)
      thenHave(relation(g)) by Tautology.fromLastStep(
        Relations.BasicTheorems.subsetIsRelationBetween of (R := f, S := g, X := A, Y := B),
        Relations.BasicTheorems.relationBetweenIsRelation of (R := g, X := A, Y := B)
      )
      thenHave(thesis) by Tautology.fromLastStep(
        Relations.BasicTheorems.relationBetweenDomainRange of (R := g)
      )
    }

    // Second, we show that for any `x ∈ dom(g)` we have `(x, y) ∈ f <=> (x, y) ∈ g`.
    have(x ∈ dom(g) |- (x, y) ∈ f <=> (x, y) ∈ g) subproof {
      assume(x ∈ dom(g))

      val `==>` = have((x, y) ∈ f |- (x, y) ∈ g) subproof {
        assume((x, y) ∈ f)

        have(x ∈ { fst(z) | z ∈ g } <=> ∃(z ∈ g, fst(z) === x)) by Replacement.apply
        thenHave(x ∈ dom(g) <=> ∃(z ∈ g, fst(z) === x)) by Substitute(dom.definition of (R := g))
        thenHave(∃(z ∈ g, fst(z) === x)) by Tautology

        val ex_z_bounded = thenHave(∃(z ∈ g, fst(z) === x)) by Tautology
        val ex_z = have(∃(z, (z ∈ g) /\ (fst(z) === x))) by Restate.from(ex_z_bounded)

        val witness_case = have((z ∈ g) /\ (fst(z) === x) |- (x, y) ∈ g) subproof {
          assume((z ∈ g) /\ (fst(z) === x))
          val z_in_g = have(z ∈ g) by Tautology
          val fstz_eq_x = have(fst(z) === x) by Tautology

          val z_in_f = have(z ∈ f) by Tautology.from(
            Subset.membership of (z := z, x := g, y := f),
            z_in_g
          )

          val z_pair = have(z === (fst(z), snd(z))) by Tautology.from(
            inversion of (f := f, z := z),
            z_in_f
          )
          val z_eq_xsnd = have(z === (x, snd(z))) by Congruence.from(z_pair, fstz_eq_x)

          val xsnd_in_g = have((x, snd(z)) ∈ g) by Congruence.from(z_in_g, z_eq_xsnd)
          val xsnd_in_f = have((x, snd(z)) ∈ f) by Tautology.from(
            Subset.membership of (z := (x, snd(z)), x := g, y := f),
            xsnd_in_g
          )

          val xy_in_f = have((x, y) ∈ f) by Hypothesis
          val x_in_dom_f = have(x ∈ dom(f)) by Tautology.from(domainMembership of (f := f, x := x, y := y), xy_in_f)

          val fx_eq_y = have(f(x) === y) by Tautology.from(
            appDefinition of (f := f, x := x, y := y),
            x_in_dom_f,
            xy_in_f
          )

          val fx_eq_snd = have(f(x) === snd(z)) by Tautology.from(
            appDefinition of (f := f, x := x, y := snd(z)),
            x_in_dom_f,
            xsnd_in_f
          )

          val y_eq_snd = have(y === snd(z)) by Congruence.from(fx_eq_y, fx_eq_snd)
          val xy_eq_xsnd = have((x, y) === (x, snd(z))) by Congruence.from(y_eq_snd)
          have((x, y) ∈ g) by Congruence.from(xsnd_in_g, xy_eq_xsnd)
        }

        val lifted = have(∃(z, (z ∈ g) /\ (fst(z) === x)) |- (x, y) ∈ g) by LeftExists(witness_case)
        have((x, y) ∈ g) by Cut(ex_z, lifted)
      }

      val `<==` = have((x, y) ∈ g |- (x, y) ∈ f) by Tautology.from(Subset.membership of (z := (x, y), x := g, y := f))

      have(thesis) by Tautology.from(`==>`, `<==`)
    }
    val equivalence = thenHave(x ∈ dom(g) |- ∀(y, (x, y) ∈ f <=> (x, y) ∈ g)) by RightForall

    // Finally, since `f` is functional on `dom(f)` it is functional on `dom(g)` as well
    // We use the equivalence shown above to replace `(x, y) ∈ f` with `(x, y) ∈ g`.
    have(functionBetween(f)(A)(B) |- ∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
    thenHave((functionBetween(f)(A)(B), x ∈ A) |- ∃!(y, (x, y) ∈ f)) by InstantiateForall(x)
    thenHave((functionBetween(f)(A)(B), x ∈ dom(f)) |- ∃!(y, (x, y) ∈ f)) by Substitute(functionBetweenDomain)
    thenHave((functionBetween(f)(A)(B), x ∈ dom(g)) |- ∃!(y, (x, y) ∈ f)) by Tautology.fromLastStep(
      domainMonotonic,
      Subset.membership of (z := x, x := dom(g), y := dom(f))
    )
    thenHave(functionBetween(f)(A)(B) |- x ∈ dom(g) ==> ∃!(y, (x, y) ∈ g)) by Tautology.fromLastStep(
      equivalence,
      Quantifiers.uniqueExistentialEquivalenceDistribution of (P := λ(y, (x, y) ∈ f), Q := λ(y, (x, y) ∈ g))
    )
    thenHave(functionBetween(f)(A)(B) |- ∀(x ∈ dom(g), ∃!(y, (x, y) ∈ g))) by RightForall

    // We put everything together and show that `g : dom(g) -> range(g)`.
    have(functionBetween(f)(A)(B) |- (functionBetween(g)(dom(g))(range(g)))) by Tautology.from(
      functionBetween.definition of (f := g, A := dom(g), B := range(g)),
      lastStep,
      `g is relation between dom(g) and range(g)`
    )

    thenHave(functionBetween(f)(A)(B) |- ∃(B, functionBetween(g)(dom(g))(B))) by RightExists
    thenHave(functionBetween(f)(A)(B) |- ∃(A, ∃(B, functionBetween(g)(A)(B)))) by RightExists
    thenHave(∃(B, functionBetween(f)(A)(B)) |- ∃(A, ∃(B, functionBetween(g)(A)(B)))) by LeftExists
    thenHave(∃(A, ∃(B, functionBetween(f)(A)(B))) |- ∃(A, ∃(B, functionBetween(g)(A)(B)))) by LeftExists
    thenHave(thesis) by Substitute(function.definition, function.definition of (f := g))
  }

  /**
   * Theorem --- If `f, g` are functions such that `g ⊆ f`, then
   * `g(x) = y` implies that `f(x) = y`.
   */
  val extensionApp = Theorem(
    (function(f), function(g), g ⊆ f, x ∈ dom(g)) |- (g(x) === y) ==> (f(x) === y)
  ) {
    assume(function(f))
    assume(function(g))
    assume(g ⊆ f)
    assume(x ∈ dom(g))

    have((g(x) === y) <=> (x, y) ∈ g) by Tautology.from(appDefinition of (f := g))
    thenHave((g(x) === y) ==> ((x, y) ∈ f)) by Tautology.fromLastStep(
      Subset.membership of (z := (x, y), x := g, y := f)
    )
    thenHave(thesis) by Tautology.fromLastStep(
      appDefinition,
      Subset.membership of (z := x, x := dom(g), y := dom(f)),
      domainMonotonic
    )
  }

  /**
   * Theorem --- If `f` is a function and `x ∉ dom(f)` then `f ∪ {(x, y)}` is a function
   * on `dom(f) ∪ {x}`.
   */
  val pointExtension = Theorem(
    (function(f), x ∉ dom(f)) |- functionOn(f ∪ singleton((x, y)))(dom(f) ∪ singleton(x))
  ) {
    assume(function(f))
    assume(x ∉ dom(f))

    val x_not_dom = have(x ∉ dom(f)) by Hypothesis

    val Rext = f ∪ singleton((x, y))

    // 1) R is a relation between Aext and Bext
    val rel_between = have(relationBetween(Rext)(dom(f) ∪ singleton(x))(range(f) ∪ singleton(y))) subproof {
      val f_rel_between = have(relationBetween(f)(dom(f))(range(f))) by Tautology.from(functionBetweenDomainRange)
      val f_subset_domrange = thenHave(f ⊆ (dom(f) × range(f))) by Substitute(relationBetween.definition of (R := f, X := dom(f), Y := range(f)))

      val dom_sub = have(dom(f) ⊆ (dom(f) ∪ singleton(x))) by Tautology.from(Union.leftSubset of (x := dom(f), y := singleton(x)))
      val ran_sub = have(range(f) ⊆ (range(f) ∪ singleton(y))) by Tautology.from(Union.leftSubset of (x := range(f), y := singleton(y)))

      val prod_sub = have((dom(f) × range(f)) ⊆ ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))) by Tautology.from(
        CartesianProduct.monotonic of (A := dom(f), B := range(f), C := (dom(f) ∪ singleton(x)), D := (range(f) ∪ singleton(y))),
        dom_sub,
        ran_sub
      )

      val f_subset_ext_prod = have(f ⊆ ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))) by Tautology.from(
        Subset.transitivity of (x := f, y := (dom(f) × range(f)), z := ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))),
        f_subset_domrange,
        prod_sub
      )

      val x_in_Aext = have(x ∈ (dom(f) ∪ singleton(x))) by Tautology.from(
        Singleton.membership of (x := x, y := x),
        Subset.membership of (x := singleton(x), y := (dom(f) ∪ singleton(x)), z := x),
        Union.rightSubset of (x := dom(f), y := singleton(x))
      )
      val y_in_Bext = have(y ∈ (range(f) ∪ singleton(y))) by Tautology.from(
        Singleton.membership of (x := y, y := y),
        Subset.membership of (x := singleton(y), y := (range(f) ∪ singleton(y)), z := y),
        Union.rightSubset of (x := range(f), y := singleton(y))
      )

      val xy_in_ext_prod = have((x, y) ∈ ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))) by Tautology.from(
        CartesianProduct.membershipSufficientCondition of (A := (dom(f) ∪ singleton(x)), B := (range(f) ∪ singleton(y)), x := x, y := y),
        x_in_Aext,
        y_in_Bext
      )

      val singleton_subset_ext_prod = have(singleton((x, y)) ⊆ ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))) by Tautology.from(
        Subset.leftSingleton of (x := (x, y), y := ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))),
        xy_in_ext_prod
      )

      val R_subset_ext_prod = have(Rext ⊆ ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))) by Tautology.from(
        Union.leftUnionSubset of (x := f, y := singleton((x, y)), z := ((dom(f) ∪ singleton(x)) × (range(f) ∪ singleton(y)))),
        f_subset_ext_prod,
        singleton_subset_ext_prod
      )

      have(thesis) by Tautology.from(
        relationBetween.definition of (R := Rext, X := (dom(f) ∪ singleton(x)), Y := (range(f) ∪ singleton(y))),
        R_subset_ext_prod
      )
    }

    // 2) R is functional on Aext
    val functional = have(∀(e1, e1 ∈ (dom(f) ∪ singleton(x)) ==> ∃!(e2, (e1, e2) ∈ Rext))) subproof {
      have(e1 ∈ (dom(f) ∪ singleton(x)) ==> ∃!(e2, (e1, e2) ∈ Rext)) subproof {
        // Fix an arbitrary e1 ∈ dom(f) ∪ {x}
        assume(e1 ∈ (dom(f) ∪ singleton(x)))
        val in_dom_or_singleton = have((e1 ∈ dom(f)) \/ (e1 ∈ singleton(x))) by Tautology.from(
          Union.membership of (x := dom(f), y := singleton(x), z := e1)
        )

        val dom_case = have(e1 ∈ dom(f) |- ∃!(e2, (e1, e2) ∈ Rext)) subproof {
          assume(e1 ∈ dom(f))

          val f_subset_R = have(f ⊆ Rext) by Tautology.from(Union.leftSubset of (x := f, y := singleton((x, y))))
          val forward = have((e1, e2) ∈ f |- (e1, e2) ∈ Rext) by Tautology.from(
            Subset.membership of (x := f, y := Rext, z := (e1, e2)),
            f_subset_R
          )

          val not_in_singleton = have((e1, e2) ∈ singleton((x, y)) |- ()) subproof {
            assume((e1, e2) ∈ singleton((x, y)))
            val pair_eq = have((e1, e2) === (x, y)) by Tautology.from(Singleton.membership of (x := (x, y), y := (e1, e2)))
            val parts = have((e1 === x) /\ (e2 === y)) by Tautology.from(Pair.extensionality of (a := e1, b := e2, c := x, d := y), pair_eq)
            val e1_eq_x = have(e1 === x) by Tautology.from(parts)
            val e1_in_dom = have(e1 ∈ dom(f)) by Hypothesis
            val x_in_dom_f = have(x ∈ dom(f)) by Congruence.from(e1_in_dom, e1_eq_x)
            have(thesis) by Tautology.from(x_in_dom_f)
          }

          val backward = have((e1, e2) ∈ Rext |- (e1, e2) ∈ f) subproof {
            assume((e1, e2) ∈ Rext)
            have(((e1, e2) ∈ f) \/ ((e1, e2) ∈ singleton((x, y)))) by Tautology.from(
              Union.membership of (x := f, y := singleton((x, y)), z := (e1, e2))
            )
            have((e1, e2) ∈ f) by Tautology.from(lastStep, not_in_singleton)
          }

          have((e1, e2) ∈ f <=> (e1, e2) ∈ Rext) by Tautology.from(forward, backward)
          val equiv_forall = thenHave(∀(e2, (e1, e2) ∈ f <=> (e1, e2) ∈ Rext)) by RightForall

          val unique_in_f0 = have(∃!(y, (e1, y) ∈ f)) by Tautology.from(functionUniqueAtDomain of (x := e1))
          val unique_in_f = have(∃!(e2, (e1, e2) ∈ f)) by Restate.from(unique_in_f0)

          val uniq_equiv = have(∃!(e2, (e1, e2) ∈ f) <=> ∃!(e2, (e1, e2) ∈ Rext)) by Tautology.from(
            Quantifiers.uniqueExistentialEquivalenceDistribution of (P := λ(e2, (e1, e2) ∈ f), Q := λ(e2, (e1, e2) ∈ Rext)),
            equiv_forall
          )
          have(∃!(e2, (e1, e2) ∈ Rext)) by Tautology.from(uniq_equiv, unique_in_f)
        }

        val singleton_case = have(e1 ∈ singleton(x) |- ∃!(e2, (e1, e2) ∈ Rext)) subproof {
          assume(e1 ∈ singleton(x))
          val e1_eq_x = have(e1 === x) by Tautology.from(Singleton.membership of (x := x, y := e1))

          // Existence for x
          val xy_in_singleton = have((x, y) ∈ singleton((x, y))) by Tautology.from(Singleton.membership of (x := (x, y), y := (x, y)))
          val xy_in_R = have((x, y) ∈ Rext) by Tautology.from(
            Union.membership of (x := f, y := singleton((x, y)), z := (x, y)),
            xy_in_singleton
          )
          val existence = have(∃(e2, (x, e2) ∈ Rext)) subproof {
            have((x, y) ∈ Rext) by Restate.from(xy_in_R)
            thenHave(thesis) by RightExists
          }

          // Uniqueness for x
          val uniqueness = have(∀(e2, ∀(T, ((x, e2) ∈ Rext) /\ ((x, T) ∈ Rext) ==> (e2 === T)))) subproof {
            have(((x, e2) ∈ Rext) /\ ((x, T) ∈ Rext) ==> (e2 === T)) subproof {
              assume(((x, e2) ∈ Rext) /\ ((x, T) ∈ Rext))
              val xe2_in_R = have((x, e2) ∈ Rext) by Tautology
              val xT_in_R = have((x, T) ∈ Rext) by Tautology

              val xe2_disj = have(((x, e2) ∈ f) \/ ((x, e2) ∈ singleton((x, y)))) by Tautology.from(
                Union.membership of (x := f, y := singleton((x, y)), z := (x, e2)),
                xe2_in_R
              )
              val xT_disj = have(((x, T) ∈ f) \/ ((x, T) ∈ singleton((x, y)))) by Tautology.from(
                Union.membership of (x := f, y := singleton((x, y)), z := (x, T)),
                xT_in_R
              )

              val not_in_f_1 = have((x, e2) ∈ f |- ()) by Tautology.from(
                domainMembership of (f := f, x := x, y := e2),
                x_not_dom
              )
              val not_in_f_2 = have((x, T) ∈ f |- ()) by Tautology.from(
                domainMembership of (f := f, x := x, y := T),
                x_not_dom
              )

              val xe2_in_singleton = have((x, e2) ∈ singleton((x, y))) by Tautology.from(xe2_disj, not_in_f_1)
              val xT_in_singleton = have((x, T) ∈ singleton((x, y))) by Tautology.from(xT_disj, not_in_f_2)

              val xe2_eq = have((x, e2) === (x, y)) by Tautology.from(Singleton.membership of (x := (x, y), y := (x, e2)), xe2_in_singleton)
              val xT_eq = have((x, T) === (x, y)) by Tautology.from(Singleton.membership of (x := (x, y), y := (x, T)), xT_in_singleton)

              val e2_eq_y = have(e2 === y) by Tautology.from(Pair.extensionality of (a := x, b := e2, c := x, d := y), xe2_eq)
              val T_eq_y = have(T === y) by Tautology.from(Pair.extensionality of (a := x, b := T, c := x, d := y), xT_eq)
              val y_eq_T = have(y === T) by Tautology.from(T_eq_y)
              have(e2 === T) by Congruence.from(e2_eq_y, y_eq_T)
            }
            thenHave(thesis) by Generalize
          }

          val conj = have(∃(e2, (x, e2) ∈ Rext) /\ ∀(e2, ∀(T, ((x, e2) ∈ Rext) /\ ((x, T) ∈ Rext) ==> (e2 === T)))) by RightAnd(existence, uniqueness)
          val unique_x = thenHave(∃!(e2, (x, e2) ∈ Rext)) by Substitute(Quantifiers.existsOneAlternativeDefinition of (x := e2, P := λ(e2, (x, e2) ∈ Rext)))

          // Transport back to e1 using e1 = x
          val x_eq_e1 = have(x === e1) by Tautology.from(e1_eq_x)
          val base = have((x === e1, ∃!(e2, (x, e2) ∈ Rext)) |- ∃!(e2, (x, e2) ∈ Rext)) by Hypothesis
          val transported = have((x === e1, ∃!(e2, (x, e2) ∈ Rext)) |- ∃!(e2, (e1, e2) ∈ Rext)) by RightSubstEq.withParameters(
            List((x, e1)),
            (Seq(T), ∃!(e2, (T, e2) ∈ Rext))
          )(base)
          have(∃!(e2, (e1, e2) ∈ Rext)) by Tautology.from(transported, x_eq_e1, unique_x)
        }

        val by_cases = have(((e1 ∈ dom(f)) \/ (e1 ∈ singleton(x))) |- ∃!(e2, (e1, e2) ∈ Rext)) by LeftOr(dom_case, singleton_case)
        have(∃!(e2, (e1, e2) ∈ Rext)) by Cut(in_dom_or_singleton, by_cases)
      }

      thenHave(thesis) by RightForall
    }

    // Assemble functionBetween and conclude
    val R_is_function_between = have(functionBetween(Rext)(dom(f) ∪ singleton(x))(range(f) ∪ singleton(y))) by Tautology.from(
      functionBetween.definition of (f := Rext, A := (dom(f) ∪ singleton(x)), B := (range(f) ∪ singleton(y))),
      rel_between,
      functional
    )

    thenHave(∃(B, functionBetween(Rext)(dom(f) ∪ singleton(x))(B))) by RightExists
    thenHave(thesis) by Substitute(functionOn.definition of (f := Rext, A := (dom(f) ∪ singleton(x))))
  }

  val functionalExtentionality = Theorem(((functionBetween(f)(A)(B)) /\ functionBetween(g)(A)(B) /\ forall(x, (x ∈ A) ==> (f(x) === g(x)))) ==> (f === g)) {
    val prem = have((functionBetween(f)(A)(B) /\ functionBetween(g)(A)(B) /\ forall(x, (x ∈ A) ==> (f(x) === g(x)))) |- (f === g)) subproof {
      assume(functionBetween(f)(A)(B) /\ functionBetween(g)(A)(B) /\ forall(x, (x ∈ A) ==> (f(x) === g(x))))

      val f_typed = have(functionBetween(f)(A)(B)) by Tautology
      val g_typed = have(functionBetween(g)(A)(B)) by Tautology
      val pointwise = have(forall(x, (x ∈ A) ==> (f(x) === g(x)))) by Tautology

      val f_on_A = have(functionOn(f)(A)) by Tautology.from(
        lisa.maths.SetTheory.Functions.BasicTheorems.functionBetweenIsFunctionOn of (f := f, A := A, B := B),
        f_typed
      )
      val g_on_A = have(functionOn(g)(A)) by Tautology.from(
        lisa.maths.SetTheory.Functions.BasicTheorems.functionBetweenIsFunctionOn of (f := g, A := A, B := B),
        g_typed
      )

      val pointwise_bounded = have(∀(x ∈ A, f(x) === g(x))) by Restate.from(pointwise)

      have(f === g) by Tautology.from(
        lisa.maths.SetTheory.Functions.BasicTheorems.extensionality of (f := f, g := g, A := A),
        f_on_A,
        g_on_A,
        pointwise_bounded
      )
    }

    have(thesis) by RightImplies(prem)
  }

  val absBodyEq = Theorem({ forall(x, (x ∈ A) ==> (Gf(x) === Hf(x))) |- abs(A)(Gf) === abs(A)(Hf) }) {
    assume(forall(x, (x ∈ A) ==> (Gf(x) === Hf(x))))
    val hyp = have(forall(x, (x ∈ A) ==> (Gf(x) === Hf(x)))) by Hypothesis

    val forward = have(z ∈ abs(A)(Gf) |- z ∈ abs(A)(Hf)) subproof {
      assume(z ∈ abs(A)(Gf))

      val in_setcomp = thenHave(z ∈ { (x, Gf(x)) | x ∈ A }) by Substitute(abs.definition of (T := A, e := Gf))
      val ex = have(∃(x ∈ A, (x, Gf(x)) === z)) by Tautology.from(
        in_setcomp,
        Replacement.membership of (y := z, x := x, A := A, F := λ(x, (x, Gf(x))))
      )

      val witness_case = have((x ∈ A) /\ ((x, Gf(x)) === z) |- z ∈ abs(A)(Hf)) subproof {
        assume((x ∈ A) /\ ((x, Gf(x)) === z))
        val x_in_A = have(x ∈ A) by Tautology
        val xG_eq_z = have((x, Gf(x)) === z) by Tautology

        val hyp_inst = have(forall(x, (x ∈ A) ==> (Gf(x) === Hf(x)))) by Hypothesis
        val pointwise_imp = thenHave((x ∈ A) ==> (Gf(x) === Hf(x))) by InstantiateForall(x)
        val Gx_eq_Hx = have(Gf(x) === Hf(x)) by Tautology.from(pointwise_imp, x_in_A)
        val Hx_eq_Gx = have(Hf(x) === Gf(x)) by Tautology.from(Gx_eq_Hx)
        val xH_eq_xG = have((x, Hf(x)) === (x, Gf(x))) by Congruence.from(Hx_eq_Gx)

        val xG_eq_xH = have((x, Gf(x)) === (x, Hf(x))) by Tautology.from(xH_eq_xG)

        val base_eq = have(((x, Gf(x)) === z, (x, Gf(x)) === (x, Hf(x))) |- (x, Gf(x)) === z) by Hypothesis
        val xH_eq_z_from = have(((x, Gf(x)) === z, (x, Gf(x)) === (x, Hf(x))) |- (x, Hf(x)) === z) by RightSubstEq.withParameters(
          List(((x, Gf(x)), (x, Hf(x)))),
          (Seq(e1), e1 === z)
        )(base_eq)
        val xH_eq_z = have((x, Hf(x)) === z) by Tautology.from(xH_eq_z_from, xG_eq_z, xG_eq_xH)

        val z_eq_xH = have(z === (x, Hf(x))) by Tautology.from(xH_eq_z)

        val xH_in_setcomp = have((x, Hf(x)) ∈ { (x, Hf(x)) | x ∈ A }) by Tautology.from(
          Replacement.map of (x := x, A := A, F := λ(x, (x, Hf(x))))
        )
        val xH_in_abs = thenHave((x, Hf(x)) ∈ abs(A)(Hf)) by Substitute(abs.definition of (T := A, e := Hf))

        val mem_base = have(((x, Hf(x)) ∈ abs(A)(Hf), (x, Hf(x)) === z) |- (x, Hf(x)) ∈ abs(A)(Hf)) by Hypothesis
        val z_in_abs_from = have(((x, Hf(x)) ∈ abs(A)(Hf), (x, Hf(x)) === z) |- z ∈ abs(A)(Hf)) by RightSubstEq.withParameters(
          List(((x, Hf(x)), z)),
          (Seq(e1), e1 ∈ abs(A)(Hf))
        )(mem_base)

        have(z ∈ abs(A)(Hf)) by Tautology.from(
          z_in_abs_from,
          xH_in_abs,
          xH_eq_z
        )
      }

      val ex_unbounded = have(∃(x, (x ∈ A) /\ ((x, Gf(x)) === z))) by Restate.from(ex)
      val lifted = have(∃(x, (x ∈ A) /\ ((x, Gf(x)) === z)) |- z ∈ abs(A)(Hf)) by LeftExists(witness_case)
      have(z ∈ abs(A)(Hf)) by Cut(ex_unbounded, lifted)
    }

    val backward = have(z ∈ abs(A)(Hf) |- z ∈ abs(A)(Gf)) by Tautology.from(forward of (Gf := Hf, Hf := Gf))

    have(z ∈ abs(A)(Gf) <=> z ∈ abs(A)(Hf)) by Tautology.from(forward, backward)
    thenHave(thesis) by Extensionality
  }

  val funcBetweenEqInFuncSpace = Theorem(functionBetween(f)(A)(B) <=> f ∈ (A ->: B)) {
    val boundSet = 𝒫(A × ⋃({ (λ(e1, B))(a) | a ∈ A }))
    val piPred = λ(
      f,
      (∀(x ∈ A, ∃!(y, (x, y) ∈ f))) /\
        (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ (λ(e1, B))(a)))))
    )
    val piSet = { f ∈ boundSet | piPred(f) }

    val piExpansionStep = have(
      f ∈ piSet <=> f ∈ boundSet /\ piPred(f)
    ) by Tautology.from(
      lisa.maths.SetTheory.Base.Comprehension.membership of (x := f, y := boundSet, φ := piPred)
    )

    val `==>` = have(functionBetween(f)(A)(B) |- f ∈ (A ->: B)) subproof {
      assume(functionBetween(f)(A)(B))

      val functionalOnA = have(∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
      val relBetween = have(relationBetween(f)(A)(B)) by Tautology.from(functionBetween.definition)
      val fSubsetAxB = thenHave(f ⊆ (A × B)) by Substitute(relationBetween.definition of (R := f, X := A, Y := B))

      val typingCheck = have(∀(e1, ∀(e2, (e1, e2) ∈ f ==> (e2 ∈ B)))) subproof {
        have((e1, e2) ∈ f ==> (e2 ∈ B)) subproof {
          assume((e1, e2) ∈ f)
          val inAxB = have((e1, e2) ∈ (A × B)) by Tautology.from(
            Subset.membership of (x := f, y := (A × B), z := (e1, e2)),
            fSubsetAxB
          )
          have(e2 ∈ B) by Tautology.from(CartesianProduct.pairMembership of (x := e1, y := e2, A := A, B := B), inAxB)
        }
        thenHave(thesis) by Generalize
      }

      val AxBsubsetAxU = have((A × B) ⊆ (A × ⋃({ B | e1 ∈ A }))) subproof {
        have(z ∈ (A × B) ==> z ∈ (A × ⋃({ B | e1 ∈ A }))) subproof {
          assume(z ∈ (A × B))

          val ex = have(∃(e1, ∃(e2, e1 ∈ A /\ (e2 ∈ B) /\ ((e1, e2) === z)))) by Tautology.from(
            CartesianProduct.membershipNecessaryCondition of (A := A, B := B)
          )

          val witnessCase = have(e1 ∈ A /\ (e2 ∈ B) /\ ((e1, e2) === z) |- z ∈ (A × ⋃({ B | e1 ∈ A }))) subproof {
            assume(e1 ∈ A /\ (e2 ∈ B) /\ ((e1, e2) === z))
            val e1InA = have(e1 ∈ A) by Tautology
            val e2InB = have(e2 ∈ B) by Tautology
            val pairEq = have((e1, e2) === z) by Tautology

            val BInFam = have(B ∈ { B | e1 ∈ A }) by Tautology.from(
              Replacement.map of (x := e1, A := A, F := λ(e1, B)),
              e1InA
            )

            val conj = have((e2 ∈ B) /\ (B ∈ { B | e1 ∈ A })) by RightAnd(e2InB, BInFam)
            val exFam = thenHave(∃(T, (e2 ∈ T) /\ (T ∈ { B | e1 ∈ A }))) by RightExists
            val e2InU = have(e2 ∈ ⋃({ B | e1 ∈ A })) by Tautology.from(unionAxiom of (x := { B | e1 ∈ A }, z := e2), exFam)

            val pairInAxU = have((e1, e2) ∈ (A × ⋃({ B | e1 ∈ A }))) by Tautology.from(
              CartesianProduct.membershipSufficientCondition of (A := A, B := ⋃({ B | e1 ∈ A }), x := e1, y := e2),
              e1InA,
              e2InU
            )
            have(z ∈ (A × ⋃({ B | e1 ∈ A }))) by Congruence.from(pairInAxU, pairEq)
          }

          val lifted1 = have(∃(e2, e1 ∈ A /\ (e2 ∈ B) /\ ((e1, e2) === z)) |- z ∈ (A × ⋃({ B | e1 ∈ A }))) by LeftExists(witnessCase)
          val lifted = have(∃(e1, ∃(e2, e1 ∈ A /\ (e2 ∈ B) /\ ((e1, e2) === z))) |- z ∈ (A × ⋃({ B | e1 ∈ A }))) by LeftExists(lifted1)
          have(z ∈ (A × ⋃({ B | e1 ∈ A }))) by Cut(ex, lifted)
        }
        thenHave(∀(z, z ∈ (A × B) ==> z ∈ (A × ⋃({ B | e1 ∈ A })))) by RightForall
        thenHave(thesis) by Substitute(⊆.definition of (x := (A × B), y := (A × ⋃({ B | e1 ∈ A }))))
      }

      val fSubsetAxU = have(f ⊆ (A × ⋃({ B | e1 ∈ A }))) by Tautology.from(
        Subset.transitivity of (x := f, y := (A × B), z := (A × ⋃({ B | e1 ∈ A }))),
        fSubsetAxB,
        AxBsubsetAxU
      )

      val boundaryCheck = have(f ∈ 𝒫(A × ⋃({ B | e1 ∈ A }))) by Tautology.from(
        PowerSet.membership of (x := f, y := (A × ⋃({ B | e1 ∈ A }))),
        fSubsetAxU
      )

      val expanded = have(
        f ∈ 𝒫(A × ⋃({ B | e1 ∈ A })) /\
          (∀(x ∈ A, ∃!(y, (x, y) ∈ f))) /\
          (∀(e1, ∀(e2, (e1, e2) ∈ f ==> (e2 ∈ B))))
      ) by Tautology.from(boundaryCheck, functionalOnA, typingCheck)

      val expandedAbs = have(
        f ∈ boundSet /\
          (∀(x ∈ A, ∃!(y, (x, y) ∈ f))) /\
          (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ (λ(e1, B))(a)))))
      ) by Restate.from(expanded)

      have(f ∈ piSet) by Tautology.from(expandedAbs, piExpansionStep)

      thenHave(thesis) by Substitute(Pi.definition of (T1 := A, T2 := λ(e1, B)))
    }

    val `<==` = have(f ∈ (A ->: B) |- functionBetween(f)(A)(B)) subproof {
      assume(f ∈ (A ->: B))
      thenHave(f ∈ piSet) by Substitute(Pi.definition of (T1 := A, T2 := λ(e1, B)))

      val expandedAbs = have(
        f ∈ boundSet /\
          (∀(x ∈ A, ∃!(y, (x, y) ∈ f))) /\
          (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ (λ(e1, B))(a)))))
      ) by Tautology.from(
        piExpansionStep,
        lastStep
      )

      val expanded = have(
        f ∈ 𝒫(A × ⋃({ B | e1 ∈ A })) /\
          (∀(x ∈ A, ∃!(y, (x, y) ∈ f))) /\
          (∀(e1, ∀(e2, (e1, e2) ∈ f ==> (e2 ∈ B))))
      ) by Restate.from(expandedAbs)

      val boundaryCheckAbs = have(f ∈ 𝒫(A × ⋃({ (λ(e1, B))(a) | a ∈ A }))) by Weakening(expandedAbs)
      val functionalOnA = have(∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Weakening(expanded)
      val typingCheck = have(∀(e1, ∀(e2, (e1, e2) ∈ f ==> (e2 ∈ B)))) by Weakening(expanded)

      val fSubsetAxU = have(f ⊆ (A × ⋃({ (λ(e1, B))(a) | a ∈ A }))) by Tautology.from(
        PowerSet.membership of (x := f, y := (A × ⋃({ (λ(e1, B))(a) | a ∈ A }))),
        boundaryCheckAbs
      )

      val fSubsetAxB = have(f ⊆ (A × B)) subproof {
        have(z ∈ f ==> z ∈ (A × B)) subproof {
          assume(z ∈ f)
          val zInF = have(z ∈ f) by Hypothesis
          val zInAxU = have(z ∈ (A × ⋃({ (λ(e1, B))(a) | a ∈ A }))) by Tautology.from(
            Subset.membership of (x := f, y := (A × ⋃({ (λ(e1, B))(a) | a ∈ A })), z := z),
            fSubsetAxU
          )

          val inv = have(∃(e1, ∃(e2, e1 ∈ A /\ (e2 ∈ ⋃({ (λ(e1, B))(a) | a ∈ A })) /\ ((e1, e2) === z)))) by Tautology.from(
            CartesianProduct.membershipNecessaryCondition of (A := A, B := ⋃({ (λ(e1, B))(a) | a ∈ A })),
            zInAxU
          )

          val witnessCase = have(e1 ∈ A /\ (e2 ∈ ⋃({ (λ(e1, B))(a) | a ∈ A })) /\ ((e1, e2) === z) |- z ∈ (A × B)) subproof {
            assume(e1 ∈ A /\ (e2 ∈ ⋃({ (λ(e1, B))(a) | a ∈ A })) /\ ((e1, e2) === z))
            val e1InA = have(e1 ∈ A) by Tautology
            val pairEq = have((e1, e2) === z) by Tautology

            val pairInF = have((e1, e2) ∈ f) by Congruence.from(zInF, pairEq)
            val imp1 = have(∀(e2, (e1, e2) ∈ f ==> (e2 ∈ B))) by InstantiateForall(e1)(typingCheck)
            val imp2 = thenHave((e1, e2) ∈ f ==> (e2 ∈ B)) by InstantiateForall(e2)
            val e2InB = have(e2 ∈ B) by Tautology.from(imp2, pairInF)

            val pairInAxB = have((e1, e2) ∈ (A × B)) by Tautology.from(
              CartesianProduct.membershipSufficientCondition of (A := A, B := B, x := e1, y := e2),
              e1InA,
              e2InB
            )
            have(z ∈ (A × B)) by Congruence.from(pairInAxB, pairEq)
          }

          val lifted1 = have(∃(e2, e1 ∈ A /\ (e2 ∈ ⋃({ (λ(e1, B))(a) | a ∈ A })) /\ ((e1, e2) === z)) |- z ∈ (A × B)) by LeftExists(witnessCase)
          val lifted = have(∃(e1, ∃(e2, e1 ∈ A /\ (e2 ∈ ⋃({ (λ(e1, B))(a) | a ∈ A })) /\ ((e1, e2) === z))) |- z ∈ (A × B)) by LeftExists(lifted1)
          have(z ∈ (A × B)) by Cut(inv, lifted)
        }

        thenHave(∀(z, z ∈ f ==> z ∈ (A × B))) by RightForall
        thenHave(thesis) by Substitute(⊆.definition of (x := f, y := (A × B)))
      }

      val relBetween = have(relationBetween(f)(A)(B)) by Tautology.from(
        fSubsetAxB,
        relationBetween.definition of (R := f, X := A, Y := B)
      )
      have(thesis) by Tautology.from(functionBetween.definition, functionalOnA, relBetween)
    }

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

}
