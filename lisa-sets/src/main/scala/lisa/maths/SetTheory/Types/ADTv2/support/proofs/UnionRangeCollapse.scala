package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.Quantifiers.existentialConjunctionWithClosedFormula
import lisa.maths.Quantifiers.existentialEquivalenceDistribution
import lisa.maths.Quantifiers.onePointRule
import lisa.maths.SetTheory.Base.Intersection.∩
import lisa.maths.SetTheory.Base._
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Functions.UnionRange.functionRangeMembership
import lisa.maths.SetTheory.Ordinals.Integer.integer
import lisa.maths.SetTheory.Ordinals.Integer.integerIsOrdinal
import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Integer.selfInSuccessor
import lisa.maths.SetTheory.Ordinals.Integer.omegaCharacterization
import lisa.maths.SetTheory.Ordinals.Integer.omegaDownwardClosed
import lisa.maths.SetTheory.Ordinals.Integer.succMembership
import lisa.maths.SetTheory.Ordinals.Integer.successorInOmega
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems._
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.BasicStepTactic.LeftExists

object UnionRangeCollapse {


  private val natSubset = Lemma(in(n, N) |- in(m, successor(n)) ==> subset(m, n)){
    import lisa.maths.SetTheory.Ordinals.TransitiveSet
    import lisa.maths.SetTheory.Ordinals.Ordinal.{ordinal, S, <=, successorMembership}

    have(in(n, N) <=> integer(n)) by InstantiateForall(n)(omegaCharacterization)
    val nIsOrdinal = have(in(n, N) |- ordinal(n)) by
      Tautology.from(lastStep, integerIsOrdinal of (α := n))

    val eqSucc = have(S(n) === successor(n)) by
      Congruence.from(S.definition of (α := n), successor.definition of (x := n))
    val succAsLeq = have(ordinal(n) |- in(m, successor(n)) <=> (m <= n)) by
      Congruence.from(successorMembership of (α := n, β := m), eqSucc)
    val succToLeq = have(in(n, N) |- in(m, successor(n)) ==> (m <= n)) by
      Tautology.from(nIsOrdinal, succAsLeq)

    val nTransitive = have(in(n, N) |- TransitiveSet.transitiveSet(n)) by
      Tautology.from(nIsOrdinal, ordinal.definition of (α := n))

    val ltCase = have((in(n, N), in(m, n)) |- subset(m, n)) by
      Tautology.from(nTransitive, TransitiveSet.elementIsSubset of (x := m, A := n))
    val eqCase = have((in(n, N), m === n) |- subset(m, n)) by
      Congruence.from(Subset.reflexivity of (x := n))

    have((in(n, N), m <= n) |- subset(m, n)) by Tautology.from(ltCase, eqCase)
    val leqToSubset = thenHave(in(n, N) |- (m <= n) ==> subset(m, n)) by Tautology

    have(thesis) by Tautology.from(succToLeq, leqToSubset)
  }

  private val intersectionNat = Lemma(in(n, N) |- n ∩ N === n){
    import lisa.maths.SetTheory.Base.Intersection.{subsetLeft}
    import lisa.maths.SetTheory.Base.Subset.rightEmpty
    val Q = lam(n, n ∩ N === n)
    
    val zeroCase = have(∅ ∩ N === ∅) subproof {
      
      have(subset(∅ ∩ N, ∅)) by Tautology.from(subsetLeft of (x := ∅, y := N))
      have(thesis) by Tautology.from(lastStep, rightEmpty of (x := ∅ ∩ N))
    }

    val recCase = have(
      in(n, N) /\ Q(n) |- Q(successor(n))
    ) subproof {
      assume(in(n, N) /\ Q(n))
      val nInNat = have(in(n, N)) by Tautology
      val ih = have(n ∩ N === n) by Tautology
      val ihSym = have(n === n ∩ N) by Tautology.from(ih)

      have(in(x, successor(n)) ==> in(x, N)) subproof {
        assume(in(x, successor(n)))
        have((x === n) \/ in(x, n)) by Tautology.from(lastStep, succMembership of (k := x, n := n))

        val eqCase = have((x === n) |- in(x, N)) by Congruence.from(nInNat)
        val inCase = have(in(x, n) |- in(x, N)) subproof {
          assume(in(x, n))
          have(in(x, n ∩ N)) by Congruence.from(lastStep, ihSym)
          have(thesis) by Tautology.from(
            lastStep,
            Intersection.membership of (z := x, x := n, y := N)
          )
        }

        have(in(x, N)) by LeftOr(eqCase, inCase)
        thenHave(thesis) by Tautology
      }

      thenHave(forall(x, in(x, successor(n)) ==> in(x, N))) by RightForall
      val succSubsetN = have(subset(successor(n), N)) by
        Tautology.from(lastStep, subsetAxiom of (x := successor(n), y := N))

      have(successor(n) ∩ N === successor(n)) by
        Tautology.from(succSubsetN, Intersection.ofSubsets of (x := successor(n), y := N))
      thenHave(thesis) by Restate
    }

    have(in(n, N) ==> (Q(n) ==> Q(successor(n)))) by Tautology.from(recCase)
    thenHave(forall(n, in(n, N) ==> (Q(n) ==> Q(successor(n))))) by RightForall
    have(Q(∅) /\ forall(n, in(n, N) ==> (Q(n) ==> Q(successor(n))))) by 
      Tautology.from(zeroCase, lastStep)

    have(forall(k, in(k, N) ==> Q(k))) by 
      Tautology.from(lastStep, omegaSuccessorInduction of (P := Q, m := n, n := k))
    thenHave(in(n, N) ==> Q(n)) by InstantiateForall(n)
    thenHave(thesis) by Tautology

  }

  private val rightAndEquivalence =
    Lemma(p1 <=> p2 |- (p1 /\ p) <=> (p2 /\ p)){
      have(thesis) by Tautology
  }

  private val restrictedFunctionRangeMembership = Lemma(
    function(f) |-
      in(y, range(restrictedFunction(f, d))) <=>
      ∃(x, in(x, d ∩ dom(f)) /\ (app(restrictedFunction(f, d))(x) === y))
  ) {

    val domAsInter = have(dom(f ↾ d) === dom(f) ∩ d) by Restate.from(
      lisa.maths.SetTheory.Functions.Operations.Restriction.domain of
        (f := f, A := d)
    )
    val interCommutative = have(dom(f) ∩ d === d ∩ dom(f)) by Restate.from(
      Intersection.commutativity of (x := dom(f), y := d)
    )
    val restrictedDom = have(dom(f ↾ d) === d ∩ dom(f)) by Tautology.from(
      domAsInter,
      interCommutative,
      altEqualityTransitivity of
        (x := dom(f ↾ d), y := dom(f) ∩ d, z := d ∩ dom(f))
    )
    have(
      function(f) |- in(y, range(restrictedFunction(f, d))) <=> ∃(
        x,
        in(x, dom(restrictedFunction(f, d))) /\
          (app(restrictedFunction(f, d))(x) === y)
      )
    ) by Cut(
      Restriction.isFunction of (A := d),
      functionRangeMembership of (f := restrictedFunction(f, d))
    )
    thenHave(
      (function(f), dom(f ↾ d) === d ∩ dom(f)) |-
        in(y, range(f ↾ d)) <=>
        ∃(x, in(x, d ∩ dom(f)) /\ (app(f ↾ d)(x) === y))
    ) by RightSubstEq.withParameters(
      List((dom(f ↾ d), d ∩ dom(f))),
      (Seq(s), in(y, range(f ↾ d)) <=> ∃(x, in(x, s) /\ (app(f ↾ d)(x) === y)))
    )
    have(
      function(f) |-
        in(y, range(f ↾ d)) <=>
        ∃(x, in(x, d ∩ dom(f)) /\ (app(f ↾ d)(x) === y))
    ) by Cut(restrictedDom, lastStep)
  }

  val unionRangeCollapse = Lemma(
    (
      function(h),
      dom(h) === N,
      in(n, N),
      forall(m, in(m, N) ==> (subset(m, n) ==> subset(app(h)(m), app(h)(n))))
    ) |- unionRange(restrictedFunction(h, successor(n))) === app(h)(n)
  ) {

    val cumulativeAssumption = ∀(m, in(m, N) ==> (subset(m, n) ==> subset(app(h)(m), app(h)(n))))
    val successorInterNat = have(in(n, N) |- successor(n) ∩ N === successor(n)) by Tautology.from(
      successorInOmega,
      equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N)),
      intersectionNat of (n := successor(n))
    )

    val normalizeRangeMembership = have(
      (function(h), in(n, N), dom(h) === N) |-
        (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)))(m) === y)
        ) /\ z ∈ y
    ) subproof {

      val domainSubset = have(in(n, N) |- successor(n) ∩ N === successor(n)) by
        Restate.from(successorInterNat)

      have(
        function(h) |- (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ (successor(n) ∩ dom(h)) /\
            (app(restrictedFunction(h, successor(n)))(m) === y)
        ) /\ z ∈ y
      ) by Cut(
        restrictedFunctionRangeMembership of (f := h, d := successor(n)),
        rightAndEquivalence of
          (
            p1 := y ∈ range(h ↾ successor(n)),
            p2 := ∃(
              m,
              m ∈ (successor(n) ∩ dom(h)) /\
                (app(restrictedFunction(h, successor(n)))(m) === y)
            ),
            p := z ∈ y
          )
      )

      thenHave(
        (function(h), dom(h) === N) |-
          (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ (successor(n) ∩ N) /\ (app(restrictedFunction(h, successor(n)))(m) === y)
          ) /\ z ∈ y
      ) by RightSubstEq.withParameters(
        List((dom(h), N)),
        (
          Seq(s),
          (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ (successor(n) ∩ s) /\ (app(restrictedFunction(h, successor(n)))(m) === y)
          ) /\ z ∈ y
        )
      )

      thenHave(
        (
          function(h),
          in(n, N),
          dom(h) === N,
          successor(n) ∩ N === successor(n)
        ) |- (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ (successor(n) ∩ N) /\ (app(restrictedFunction(h, successor(n)))(m) === y)
        ) /\ z ∈ y
      ) by Weakening

      thenHave(
        (
          function(h),
          in(n, N),
          dom(h) === N,
          successor(n) ∩ N === successor(n)
        ) |- (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)))(m) === y)
        ) /\ z ∈ y
      ) by RightSubstEq.withParameters(
        List((successor(n) ∩ N, successor(n))),
        (
          Seq(s),
          (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=>
            ∃(m, m ∈ s /\ (app(restrictedFunction(h, successor(n)))(m) === y)) /\ z ∈ y
        )
      )

      have(thesis) by Cut(domainSubset, lastStep)
    }

    val rangeWitnessToSuccessorWitness = have(
      (function(h), in(n, N), dom(h) === N) |-
        ∃(y, y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=>
        ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m))
    ) subproof {
      have(
        (function(h), in(n, N), dom(h) === N) |-
          (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)))(m) === y) /\ z ∈ y
          )
      ) by Tautology.from(
        equivalenceRewriting,
        normalizeRangeMembership,
        existentialConjunctionWithClosedFormula of
          (
            P :=
              lam(m, m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)))(m) === y)),
            p := z ∈ y
          )
      )

      thenHave(
        (function(h), in(n, N), dom(h) === N) |- ∀(
          y,
          (y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)))(m) === y) /\ z ∈ y
          )
        )
      ) by RightForall

      have(
        (function(h), in(n, N), dom(h) === N) |-
          ∃(y, y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
            y,
            ∃(
              m,
              m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)))(m) === y) /\ z ∈ y
            )
          )
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of
          (
            P := lam(y, y ∈ range(h ↾ successor(n)) /\ z ∈ y),
            Q := lam(
              y,
              ∃(
                m,
                m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)))(m) === y) /\
                  z ∈ y
              )
            )
          )
      )

      val introM = thenHave(
        (function(h), in(n, N), dom(h) === N) |-
          ∃(y, y ∈ range(h ↾ successor(n)) /\ z ∈ y) <=> ∃(
            m,
            ∃(
              y,
              m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)))(m) === y)
            )
          )
      ) by Tableau

      have(
        (∃(
          x,
          lam(y, m ∈ successor(n) /\ z ∈ y)(x) /\
            (app(restrictedFunction(h, successor(n)))(m) === x)
        )) <=> lam(y, m ∈ successor(n) /\ z ∈ y)(app(restrictedFunction(h, successor(n)))(m))
      ) by Tautology.from(
        onePointRule of
          (
            y := app(restrictedFunction(h, successor(n)))(m),
            P := lam(y, m ∈ successor(n) /\ z ∈ y)
          )
      )
      have(
        (∃(
          y,
          m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)))(m) === y)
        )) <=> (m ∈ successor(n) /\ z ∈ app(restrictedFunction(h, successor(n)))(m))
      ) by Tautology.from(lastStep of (x := y), BetaReduction)
      val onePointExpanded = lastStep

      val domProof = have((in(n, N), dom(h) === N, m ∈ successor(n)) |- in(m, dom(h))) subproof {
        assume(in(n, N))
        assume(dom(h) === N)
        assume(m ∈ successor(n))
        val succAsInter = have(successor(n) === successor(n) ∩ N) by Tautology.from(successorInterNat)
        have(m ∈ successor(n)) by Hypothesis
        have(m ∈ (successor(n) ∩ N)) by Congruence.from(lastStep, succAsInter)
        have(m ∈ N) by Tautology.from(
          lastStep,
          Intersection.membership of (z := m, x := successor(n), y := N)
        )
        have(thesis) by Congruence.from(lastStep)
      }

      have(
        (function(h), in(n, N), dom(h) === N, m ∈ successor(n)) |-
          (∃(
            y,
            m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)))(m) === y)
          )) <=> (m ∈ successor(n) /\ z ∈ app(h)(m))
      ) by Congruence.from(
        Restriction.restrictedApp of (f := h, x := m, A := successor(n)),
        domProof,
        onePointExpanded
      )
      thenHave(
        (function(h), in(n, N), dom(h) === N) |-
        (∃(
          y,
          m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)))(m) === y)
        )) <=> (m ∈ successor(n) /\ z ∈ app(h)(m))
      ) by Tableau

      thenHave(
        (function(h), in(n, N), dom(h) === N) |- ∀(
          m,
          (∃(
            y,
            m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)))(m) === y)
          )) <=> (m ∈ successor(n) /\ z ∈ app(h)(m))
        )
      ) by RightForall

      have(
        (function(h), in(n, N), dom(h) === N) |- ∃(
          m,
          ∃(
            y,
            m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)))(m) === y)
          )
        ) <=> ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m))
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of
          (
            P := lam(
              m,
              ∃(
                y,
                m ∈ successor(n) /\ z ∈ y /\
                  (app(restrictedFunction(h, successor(n)))(m) === y)
              )
            ),
            Q := lam(m, m ∈ successor(n) /\ z ∈ app(h)(m))
          )
      )

      have(thesis) by Tautology.from(equivalenceRewriting, introM, lastStep)
    }

    val unionIsExists = have(
      (function(h), in(n, N), dom(h) === N) |- z ∈ unionRange(
        restrictedFunction(h, successor(n))
      ) <=> ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m))
    ) by Tautology.from(
      rangeWitnessToSuccessorWitness,
      unionAxiom of (x := range(h ↾ successor(n))),
      equivalenceRewriting of
        (
          p1 := z ∈ unionRange(restrictedFunction(h, successor(n))),
          p2 := ∃(y, y ∈ range(h ↾ successor(n)) /\ z ∈ y),
          p3 := ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m))
        )
    )

    val cumulativeEquivalence = have(
      (cumulativeAssumption, in(n, N)) |- ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m)) <=> z ∈ app(h)(n)
    ) subproof {
      val toExists = {
        val seq1 = have(z ∈ app(h)(n) |- z ∈ app(h)(n)) by Hypothesis
        have(z ∈ app(h)(n) |- n ∈ successor(n) /\ z ∈ app(h)(n)) by
          RightAnd(seq1, selfInSuccessor of (n := n))
        thenHave(z ∈ app(h)(n) |- ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m))) by RightExists
        thenHave((cumulativeAssumption, in(n, N)) |- z ∈ app(h)(n) ==> ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m))) by
          Weakening
      }

      val toValue = {
        have(cumulativeAssumption |- cumulativeAssumption) by Hypothesis
        val cumulativeAtM = thenHave(cumulativeAssumption |- in(m, N) ==> (subset(m, n) ==> subset(app(h)(m), app(h)(n)))) by
          InstantiateForall(m)

        val succToSubset = have((in(n, N), m ∈ successor(n)) |- subset(m, n)) by Tautology.from(natSubset)

        val succIsNatStep = have(in(n, N) |- in(successor(n), N)) by Tautology.from(
          successorInOmega,
          equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N))
        )
        val succElemNat = have((in(n, N), m ∈ successor(n)) |- in(m, N)) by Tautology.from(
          succIsNatStep,
          omegaDownwardClosed of (x := m, y := successor(n))
        )

        have(
          (cumulativeAssumption, in(n, N), m ∈ successor(n)) |- subset(app(h)(m), app(h)(n))
        ) by Tautology.from(cumulativeAtM, succElemNat, succToSubset)

        have(
          (cumulativeAssumption, in(n, N), m ∈ successor(n)) |- forall(z, z ∈ app(h)(m) ==> z ∈ app(h)(n))
        ) by Tautology.from(lastStep, subsetAxiom of (x := app(h)(m), y := app(h)(n)))
        thenHave((cumulativeAssumption, in(n, N), m ∈ successor(n) /\ z ∈ app(h)(m)) |- z ∈ app(h)(n)) by
          InstantiateForall(z)
        thenHave(
          (cumulativeAssumption, in(n, N), ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m))) |- z ∈ app(h)(n)
        ) by LeftExists
        thenHave((cumulativeAssumption, in(n, N)) |- ∃(m, m ∈ successor(n) /\ z ∈ app(h)(m)) ==> z ∈ app(h)(n)) by
          RightImplies
      }

      have(thesis) by RightIff(toValue, toExists)
    }

    have(
      (function(h), in(n, N), dom(h) === N, cumulativeAssumption) |-
        (z ∈ unionRange(restrictedFunction(h, successor(n)))) <=> z ∈ app(h)(n)
    ) by Tautology.from(equivalenceRewriting, unionIsExists, cumulativeEquivalence)
    thenHave(
      (function(h), in(n, N), dom(h) === N, cumulativeAssumption) |-
        ∀(z, z ∈ unionRange(restrictedFunction(h, successor(n))) <=> z ∈ app(h)(n))
    ) by RightForall

    have(thesis) by Tautology.from(
      equivalenceApply,
      lastStep,
      extensionalityAxiom of
        (x := unionRange(restrictedFunction(h, successor(n))), y := app(h)(n))
    )

  }

}
