package lisa.maths.SetTheory.Functions

import lisa.maths.Quantifiers.existentialConjunctionWithClosedFormula
import lisa.maths.Quantifiers.existentialEquivalenceDistribution
import lisa.maths.Quantifiers.onePointRule
import lisa.maths.SetTheory.Base.Pair.fst
import lisa.maths.SetTheory.Base.Pair.given_Conversion_Expr_Expr_Expr
import lisa.maths.SetTheory.Base.Pair.snd
import lisa.maths.SetTheory.Base._
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}

/**
 * Membership characterizations for the range and the union of the range of a
 * function:
 *   - `y ∈ range(f) ⇔ ∃x ∈ dom(f). f(x) = y`
 *   - `z ∈ ⋃range(h) ⇔ ∃n ∈ dom(h). z ∈ h(n)`
 */
object UnionRange {

  private val f, g, h = variable[Ind]
  private val R = variable[Ind]
  private val x, y, z = variable[Ind]
  private val m, n = variable[Ind]
  private val p = variable[Prop]
  private val P, Q = variable[Ind >>: Prop]

  val functionRangeMembership = Lemma(
    function(f) |-
      (y ∈ range(f)) <=> ∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))
  ) {
    val witnessToDomainApp = have(
      (function(f), z ∈ f, snd(z) === y) |- ∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))
    ) subproof {
      assume(function(f))
      assume(z ∈ f)
      assume(snd(z) === y)

      val zPair = have(z === (fst(z), snd(z))) by Tautology.from(
        lisa.maths.SetTheory.Functions.BasicTheorems.inversion
      )
      val pairInF = have((fst(z), snd(z)) ∈ f) by Congruence.from(zPair)
      val fstInDom = have(fst(z) ∈ dom(f)) by Tautology.from(
        pairInF,
        lisa.maths.SetTheory.Functions.BasicTheorems.domainMembership of (x := fst(z), y := snd(z))
      )

      val appDef = have((app(f)(fst(z)) === snd(z)) <=> ((fst(z), snd(z)) ∈ f)) by Tautology.from(
        lisa.maths.SetTheory.Functions.BasicTheorems.appDefinition of (x := fst(z), y := snd(z)),
        fstInDom
      )
      val appEqSnd = have(app(f)(fst(z)) === snd(z)) by Tautology.from(appDef, pairInF)
      val appEqY = have(app(f)(fst(z)) === y) by Congruence.from(appEqSnd)

      have((fst(z) ∈ dom(f)) /\ (app(f)(fst(z)) === y)) by Tautology.from(fstInDom, appEqY)
      thenHave(∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))) by RightExists
    }

    val forward = have(function(f) |- (y ∈ range(f)) ==> ∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))) subproof {
      assume(function(f))
      assume(y ∈ range(f))

      import lisa.maths.SetTheory.Base.Replacement.{|}

      have(y ∈ { snd(z) | z ∈ f } <=> ∃(z ∈ f, snd(z) === y)) by Replacement.apply
      thenHave(y ∈ range(f) <=> ∃(z, (z ∈ f) /\ (snd(z) === y))) by Substitute(range.definition of (R := f))
      val exWitness = have(∃(z, (z ∈ f) /\ (snd(z) === y))) by Tautology.from(lastStep)

      have(((z ∈ f) /\ (snd(z) === y)) |- function(f) ==> ∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))) by
        Tautology.from(witnessToDomainApp)
      val liftWitness = have(∃(z, (z ∈ f) /\ (snd(z) === y)) |- function(f) ==> ∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))) by
        LeftExists(lastStep)

      have((y ∈ range(f)) |- function(f) ==> ∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))) by Cut(exWitness, liftWitness)
      thenHave(thesis) by Tautology
    }

    val domainAppToRange = have(
      (function(f), x ∈ dom(f), app(f)(x) === y) |- y ∈ range(f)
    ) subproof {
      assume(function(f))
      assume(x ∈ dom(f))
      assume(app(f)(x) === y)

      have(x ∈ dom(f)) by Hypothesis
      val appDef = have((app(f)(x) === y) <=> ((x, y) ∈ f)) by Tautology.from(
        lisa.maths.SetTheory.Functions.BasicTheorems.appDefinition of (x := x, y := y),
        lastStep
      )
      have(app(f)(x) === y) by Hypothesis
      val pairInF = have((x, y) ∈ f) by Tautology.from(appDef, lastStep)
      have(y ∈ range(f)) by Tautology.from(
        pairInF,
        lisa.maths.SetTheory.Functions.BasicTheorems.rangeMembership of (x := x, y := y)
      )
    }

    val backward = have(function(f) |- (∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))) ==> (y ∈ range(f))) subproof {
      assume(function(f))
      assume(∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y)))

      have((function(f), (x ∈ dom(f)) /\ (app(f)(x) === y)) |- y ∈ range(f)) by
        Tautology.from(domainAppToRange)
      thenHave((function(f), ∃(x, (x ∈ dom(f)) /\ (app(f)(x) === y))) |- y ∈ range(f)) by LeftExists
      thenHave(thesis) by Tautology
    }

    have(thesis) by Tautology.from(forward, backward)
  }

  val unionRangeMembership = Lemma(
    function(h) |-
      (z ∈ ⋃(range(h))) <=> ∃(n, (n ∈ dom(h)) /\ (z ∈ app(h)(n)))
  ) {
    val iffAfterAnd = have(
      function(h) |- (y ∈ range(h) /\ z ∈ y) <=>
        ∃(m, (m ∈ dom(h)) /\ (app(h)(m) === y)) /\ z ∈ y
    ) by Tautology.from(functionRangeMembership of (f := h))
    have(
      function(h) |- (y ∈ range(h) /\ z ∈ y) <=>
        ∃(m, (m ∈ dom(h)) /\ (app(h)(m) === y) /\ z ∈ y)
    ) by Tautology.from(
      iffAfterAnd,
      existentialConjunctionWithClosedFormula of
        (P := lambda(m, (m ∈ dom(h)) /\ (app(h)(m) === y)), p := z ∈ y)
    )

    thenHave(
      function(h) |- ∀(
        y,
        (y ∈ range(h) /\ z ∈ y) <=>
          ∃(m, (m ∈ dom(h)) /\ (app(h)(m) === y) /\ z ∈ y)
      )
    ) by RightForall

    val beforeExSwap = have(
      function(h) |-
        ∃(y, y ∈ range(h) /\ z ∈ y) <=>
        ∃(y, ∃(m, (m ∈ dom(h)) /\ (app(h)(m) === y) /\ z ∈ y))
    ) by Cut(
      lastStep,
      existentialEquivalenceDistribution of
        (
          P := lambda(y, y ∈ range(h) /\ z ∈ y),
          Q := lambda(y, ∃(m, (m ∈ dom(h)) /\ (app(h)(m) === y) /\ z ∈ y))
        )
    )

    have(
      ∃(y, ∃(m, (m ∈ dom(h)) /\ (app(h)(m) === y) /\ z ∈ y)) <=>
        ∃(m, ∃(y, (m ∈ dom(h)) /\ z ∈ y /\ (app(h)(m) === y)))
    ) by Tableau

    val introM = have(
      function(h) |-
        ∃(y, y ∈ range(h) /\ z ∈ y) <=>
        ∃(m, ∃(y, (m ∈ dom(h)) /\ z ∈ y /\ (app(h)(m) === y)))
    ) by Tautology.from(beforeExSwap, lastStep)

    have(
      ∀(
        m,
        (∃(y, (m ∈ dom(h)) /\ z ∈ y /\ (app(h)(m) === y))) <=>
          ((m ∈ dom(h)) /\ z ∈ app(h)(m))
      )
    ) by RightForall(
      onePointRule of (P := lambda(y, (m ∈ dom(h)) /\ z ∈ y), y := app(h)(m))
    )

    have(
      ∃(m, ∃(y, (m ∈ dom(h)) /\ z ∈ y /\ (app(h)(m) === y))) <=>
        ∃(m, (m ∈ dom(h)) /\ z ∈ app(h)(m))
    ) by Cut(
      lastStep,
      existentialEquivalenceDistribution of
        (
          P := lambda(m, ∃(y, (m ∈ dom(h)) /\ z ∈ y /\ (app(h)(m) === y))),
          Q := lambda(m, (m ∈ dom(h)) /\ z ∈ app(h)(m))
        )
    )

    have(
      function(h) |-
        ∃(y, y ∈ range(h) /\ z ∈ y) <=>
        ∃(m, (m ∈ dom(h)) /\ z ∈ app(h)(m))
    ) by Tautology.from(introM, lastStep)

    val p_1 = ∃(y, y ∈ range(h) /\ z ∈ y)
    val p_2 = ∃(n, (n ∈ dom(h)) /\ z ∈ app(h)(n))

    have(function(h) |- (z ∈ ⋃(range(h)) <=> p_1) /\ (p_1 <=> p_2)) by
      Tautology.from(unionAxiom of (x := range(h)), lastStep)
    have(thesis) by Tautology.from(lastStep)
  }

  /**
   * Theorem --- `⋃range` is monotonic: if `f ⊆ g` then `⋃range(f) ⊆ ⋃range(g)`.
   */
  val unionRangeMonotonic = Lemma(f ⊆ g |- ⋃(range(f)) ⊆ ⋃(range(g))) {
    val rf = range(f)
    val rg = range(g)

    have(rf ⊆ rg ==> ⋃(rf) ⊆ ⋃(rg)) by
      Tautology.from(Union.unaryMonotonic of (x := rf, y := rg))
    have(f ⊆ g |- ⋃(rf) ⊆ ⋃(rg)) by
      Tautology.from(lastStep, BasicTheorems.rangeMonotonic of (g := f, f := g))
    thenHave(thesis) by Restate
  }

}
