package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.Quantifiers.∃!

import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.UnionRangeCollapse.*

import lisa.maths.SetTheory.Base.*
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base.Intersection.∩
import lisa.maths.SetTheory.Ordinals.*
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.maths.Quantifiers.{
  existentialConjunctionWithClosedFormula,
  existentialEquivalenceDistribution,
  onePointRule
}


object UnionRangeMembership {

  private val n, m = variable[Ind]
  private val s, t, d = variable[Ind]
  private val x, y, z = variable[Ind]
  private val f, g, h = variable[Ind]
  private val p1, p2, p3 = variable[Prop]
  private val q1, q2 = variable[Prop]
  private val P = variable[Ind >>: Prop]
  private val P2 = variable[Ind >>: Ind >>: Prop]



  // Synonyms for portability

  private def relationDomain(f: Expr[Ind]): Expr[Ind] = dom(f)

  private def functional(f: Expr[Ind]): Expr[Prop] = function(f)

  private def relationRange(f: Expr[Ind]): Expr[Ind] = range(f)

  private def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] = 
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  // Some useful lemmas

  private val existentialSwap = Lemma(∃(x, ∃(y, P2(x)(y))) <=> ∃(y, ∃(x, P2(x)(y)))) {
    have(thesis) by Tableau
  }

  val unionRangeMembership = Lemma(
    functional(h) |-
      in(z, unionRange(h)) <=> exists(n, in(n, dom(h)) /\ in(z, app(h, n)))
  ) {
    val iffAfterAnd = have(
      functional(h) |- (y ∈ relationRange(h) /\ z ∈ y) <=>
        ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y)) /\ z ∈ y
    ) by Cut(
      functionRangeMembership of (f := h),
      rightAndEquivalence of
        (
          p1 := y ∈ relationRange(h),
          p2 := ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y)),
          p := z ∈ y
        )
    )
    have(
      functional(h) |- (y ∈ relationRange(h) /\ z ∈ y) <=>
        ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)
    ) by Tautology.from(equivalenceRewriting,
      iffAfterAnd,
      existentialConjunctionWithClosedFormula of
        (P := lambda(m, m ∈ relationDomain(h) /\ (app(h, m) === y)), p := z ∈ y)
    )

    thenHave(
      functional(h) |- ∀(
        y,
        (y ∈ relationRange(h) /\ z ∈ y) <=>
          ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)
      )
    ) by RightForall

    val beforeExSwap = have(
      functional(h) |-
        ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=>
        ∃(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))
    ) by Cut(
      lastStep,
      existentialEquivalenceDistribution of
        (
          P := lambda(y, y ∈ relationRange(h) /\ z ∈ y),
          Q := lambda(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))
        )
    )

    have(
      ∃(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) <=>
        ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))
    ) subproof {

      have(
        m ∈ relationDomain(h) /\
          (app(h, m) === y) /\ z ∈ y <=>
          m ∈ relationDomain(h) /\ z ∈ y /\
          (app(h, m) === y)
      ) by Restate
      thenHave(forall(
        y,
        m ∈ relationDomain(h) /\
          (app(h, m) === y) /\ z ∈ y <=>
          m ∈ relationDomain(h) /\ z ∈ y /\
          (app(h, m) === y)
      )) by RightForall
      have(
        ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y) <=>
          ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of
          (
            P := lambda(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y),
            Q := lambda(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))
          )
      )
      thenHave(forall(
        m,
        ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y) <=>
          ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))
      )) by RightForall
      have(
        ∃(m, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) <=>
          ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of
          (
            P := lambda(y, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)),
            Q := lambda(y, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))
          )
      )
      have(thesis) by Tautology.from(equivalenceRewriting,
        lastStep,
        existentialSwap of
          (P2 := λ(y, λ(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)))
      )
    }

    val introM = have(
      functional(h) |-
        ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=>
        ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))
    ) by Tautology.from(equivalenceRewriting, beforeExSwap, lastStep)

    have(∀(
      m,
      (∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) <=>
        (m ∈ relationDomain(h) /\ z ∈ app(h, m))
    )) by RightForall(
      onePointRule of (P := lambda(y, m ∈ relationDomain(h) /\ z ∈ y), y := app(h, m))
    )

    have(
      ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) <=>
        ∃(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))
    ) by Cut(
      lastStep,
      existentialEquivalenceDistribution of
        (
          P := lambda(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))),
          Q := lambda(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))
        )
    )

    have(
      functional(h) |-
        ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=>
        ∃(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))
    ) by Tautology.from(equivalenceRewriting, introM, lastStep)

    val p_1 = z ∈ ⋃(range(h))
    val p_2 = ∃(y, y ∈ relationRange(h) /\ z ∈ y)
    val p_3 = ∃(n, n ∈ relationDomain(h) /\ z ∈ app(h, n))

    have(functional(h) |- (z ∈ ⋃(range(h)) <=> p_2) /\ (p_2 <=> p_3)) by 
      Tautology.from(unionAxiom of (x := range(h)), lastStep)
    have(thesis) by Tautology.from(lastStep, equivalenceRewriting)

  }

}
