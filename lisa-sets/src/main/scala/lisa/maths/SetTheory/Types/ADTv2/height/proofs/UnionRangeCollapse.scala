package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.Quantifiers.existentialConjunctionWithClosedFormula
import lisa.maths.Quantifiers.existentialEquivalenceDistribution
import lisa.maths.Quantifiers.onePointRule
import lisa.maths.SetTheory.Base.Intersection.∩
import lisa.maths.SetTheory.Base._
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
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
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts._
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.BasicStepTactic.LeftExists

object UnionRangeCollapse {

  private val natSubset = Lemma(n ∈ N |- m ∈ S(n) ==> m ⊆ n) {
    import lisa.maths.SetTheory.Ordinals.TransitiveSet
    import lisa.maths.SetTheory.Ordinals.Ordinal.{ordinal, S, <=, successorMembership}

    have(n ∈ N <=> integer(n)) by InstantiateForall(n)(omegaCharacterization)
    val nIsOrdinal = have(n ∈ N |- ordinal(n)) by
      Tautology.from(lastStep, integerIsOrdinal of (α := n))

    val succAsLeq = have(ordinal(n) |- m ∈ S(n) <=> (m <= n)) by
      Tautology.from(successorMembership of (α := n, β := m))
    val succToLeq = have(n ∈ N |- m ∈ S(n) ==> (m <= n)) by
      Tautology.from(nIsOrdinal, succAsLeq)

    val nTransitive = have(n ∈ N |- TransitiveSet.transitiveSet(n)) by
      Tautology.from(nIsOrdinal, ordinal.definition of (α := n))

    val ltCase = have((n ∈ N, m ∈ n) |- m ⊆ n) by
      Tautology.from(nTransitive, TransitiveSet.elementIsSubset of (x := m, A := n))
    val eqCase = have((n ∈ N, m === n) |- m ⊆ n) by
      Congruence.from(Subset.reflexivity of (x := n))

    have((n ∈ N, m <= n) |- m ⊆ n) by Tautology.from(ltCase, eqCase)
    val leqToSubset = thenHave(n ∈ N |- (m <= n) ==> m ⊆ n) by Tautology

    have(thesis) by Tautology.from(succToLeq, leqToSubset)
  }

  private val intersectionNat = Lemma(n ∈ N |- n ∩ N === n) {
    import lisa.maths.SetTheory.Base.Intersection.{subsetLeft}
    import lisa.maths.SetTheory.Base.Subset.rightEmpty
    val Q = λ(n, n ∩ N === n)

    val zeroCase = have(∅ ∩ N === ∅) subproof {

      have(∅ ∩ N ⊆ ∅) by Tautology.from(subsetLeft of (x := ∅, y := N))
      have(thesis) by Tautology.from(lastStep, rightEmpty of (x := ∅ ∩ N))
    }

    val recCase = have(
      n ∈ N /\ Q(n) |- Q(S(n))
    ) subproof {
      assume(n ∈ N /\ Q(n))
      val nInNat = have(n ∈ N) by Tautology
      val ih = have(n ∩ N === n) by Tautology
      val ihSym = have(n === n ∩ N) by Tautology.from(ih)

      have(x ∈ S(n) ==> x ∈ N) subproof {
        assume(x ∈ S(n))
        val splitFact = have((x === n) \/ (x ∈ n)) by
          Tautology.from(lastStep, succMembership of (k := x, n := n))

        val eqCase = have((x === n) |- x ∈ N) by Congruence.from(nInNat)
        val inCase = have(x ∈ n |- x ∈ N) subproof {
          assume(x ∈ n)
          have(x ∈ (n ∩ N)) by Congruence.from(lastStep, ihSym)
          have(thesis) by Tautology.from(
            lastStep,
            Intersection.membership of (z := x, x := n, y := N)
          )
        }

        val splitCases = have((x === n) \/ (x ∈ n) |- x ∈ N) by LeftOr(eqCase, inCase)
        have(x ∈ N) by Cut(splitFact, splitCases)
        thenHave(thesis) by RightImplies.withParameters(x ∈ S(n), x ∈ N)
      }

      thenHave(forall(x, x ∈ S(n) ==> x ∈ N)) by RightForall
      val succSubsetN = have(S(n) ⊆ N) by
        Tautology.from(lastStep, subsetAxiom of (x := S(n), y := N))

      have(S(n) ∩ N === S(n)) by
        Tautology.from(succSubsetN, Intersection.ofSubsets of (x := S(n), y := N))
      thenHave(thesis) by Restate
    }

    have(n ∈ N ==> (Q(n) ==> Q(S(n)))) by Tautology.from(recCase)
    thenHave(forall(n, n ∈ N ==> (Q(n) ==> Q(S(n))))) by RightForall
    have(Q(∅) /\ forall(n, n ∈ N ==> (Q(n) ==> Q(S(n))))) by
      Tautology.from(zeroCase, lastStep)

    have(forall(k, k ∈ N ==> Q(k))) by
      Tautology.from(lastStep, omegaSuccessorInduction of (P := Q, m := n, n := k))
    thenHave(n ∈ N ==> Q(n)) by InstantiateForall(n)
    thenHave(thesis) by Tautology

  }

  private val rightAndEquivalence =
    Lemma(p1 <=> p2 |- (p1 /\ p) <=> (p2 /\ p)) {
      have(thesis) by Tautology
    }

  private val restrictedFunctionRangeMembership = Lemma(
    function(f) |-
      y ∈ range(f ↾ d) <=>
      ∃(x, x ∈ (d ∩ dom(f)) /\ (app(f ↾ d)(x) === y))
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
      function(f) |- y ∈ range(f ↾ d) <=> ∃(
        x,
        x ∈ dom(f ↾ d) /\
          (app(f ↾ d)(x) === y)
      )
    ) by Cut(
      Restriction.isFunction of (A := d),
      functionRangeMembership of (f := f ↾ d)
    )
    thenHave(
      (function(f), dom(f ↾ d) === d ∩ dom(f)) |-
        y ∈ range(f ↾ d) <=>
        ∃(x, x ∈ (d ∩ dom(f)) /\ (app(f ↾ d)(x) === y))
    ) by RightSubstEq.withParameters(
      List((dom(f ↾ d), d ∩ dom(f))),
      (Seq(s), y ∈ range(f ↾ d) <=> ∃(x, x ∈ s /\ (app(f ↾ d)(x) === y)))
    )
    have(
      function(f) |-
        y ∈ range(f ↾ d) <=>
        ∃(x, x ∈ (d ∩ dom(f)) /\ (app(f ↾ d)(x) === y))
    ) by Cut(restrictedDom, lastStep)
  }

  val unionRangeCollapse = Lemma(
    (
      function(h),
      dom(h) === N,
      n ∈ N,
      forall(m, m ∈ N ==> (m ⊆ n ==> app(h)(m) ⊆ app(h)(n)))
    ) |- ⋃(range(h ↾ S(n))) === app(h)(n)
  ) {

    val cumulativeAssumption = ∀(m, m ∈ N ==> (m ⊆ n ==> app(h)(m) ⊆ app(h)(n)))
    val successorInterNat = have(n ∈ N |- S(n) ∩ N === S(n)) by Tautology.from(
      successorInOmega,
      equivalenceApply of (p1 := n ∈ N, p2 := S(n) ∈ N),
      intersectionNat of (n := S(n))
    )

    val normalizeRangeMembership = have(
      (function(h), n ∈ N, dom(h) === N) |-
        (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ S(n) /\ (app(h ↾ S(n))(m) === y)
        ) /\ z ∈ y
    ) subproof {

      val domainSubset = have(n ∈ N |- S(n) ∩ N === S(n)) by
        Restate.from(successorInterNat)

      have(
        function(h) |- (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ (S(n) ∩ dom(h)) /\
            (app(h ↾ S(n))(m) === y)
        ) /\ z ∈ y
      ) by Cut(
        restrictedFunctionRangeMembership of (f := h, d := S(n)),
        rightAndEquivalence of
          (
            p1 := y ∈ range(h ↾ S(n)),
            p2 := ∃(
              m,
              m ∈ (S(n) ∩ dom(h)) /\
                (app(h ↾ S(n))(m) === y)
            ),
            p := z ∈ y
          )
      )

      thenHave(
        (function(h), dom(h) === N) |-
          (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ (S(n) ∩ N) /\ (app(h ↾ S(n))(m) === y)
          ) /\ z ∈ y
      ) by RightSubstEq.withParameters(
        List((dom(h), N)),
        (
          Seq(s),
          (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ (S(n) ∩ s) /\ (app(h ↾ S(n))(m) === y)
          ) /\ z ∈ y
        )
      )

      thenHave(
        (
          function(h),
          n ∈ N,
          dom(h) === N,
          S(n) ∩ N === S(n)
        ) |- (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ (S(n) ∩ N) /\ (app(h ↾ S(n))(m) === y)
        ) /\ z ∈ y
      ) by Weakening

      thenHave(
        (
          function(h),
          n ∈ N,
          dom(h) === N,
          S(n) ∩ N === S(n)
        ) |- (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ S(n) /\ (app(h ↾ S(n))(m) === y)
        ) /\ z ∈ y
      ) by RightSubstEq.withParameters(
        List((S(n) ∩ N, S(n))),
        (
          Seq(s),
          (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=>
            ∃(m, m ∈ s /\ (app(h ↾ S(n))(m) === y)) /\ z ∈ y
        )
      )

      have(thesis) by Cut(domainSubset, lastStep)
    }

    val rangeWitnessToSuccessorWitness = have(
      (function(h), n ∈ N, dom(h) === N) |-
        ∃(y, y ∈ range(h ↾ S(n)) /\ z ∈ y) <=>
        ∃(m, m ∈ S(n) /\ z ∈ app(h)(m))
    ) subproof {
      have(
        (function(h), n ∈ N, dom(h) === N) |-
          (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ S(n) /\ (app(h ↾ S(n))(m) === y) /\ z ∈ y
          )
      ) by Tautology.from(
        equivalenceRewriting,
        normalizeRangeMembership,
        existentialConjunctionWithClosedFormula of
          (
            P :=
              λ(m, m ∈ S(n) /\ (app(h ↾ S(n))(m) === y)),
            p := z ∈ y
          )
      )

      thenHave(
        (function(h), n ∈ N, dom(h) === N) |- ∀(
          y,
          (y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
            m,
            m ∈ S(n) /\ (app(h ↾ S(n))(m) === y) /\ z ∈ y
          )
        )
      ) by RightForall

      have(
        (function(h), n ∈ N, dom(h) === N) |-
          ∃(y, y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
            y,
            ∃(
              m,
              m ∈ S(n) /\ (app(h ↾ S(n))(m) === y) /\ z ∈ y
            )
          )
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of
          (
            P := λ(y, y ∈ range(h ↾ S(n)) /\ z ∈ y),
            Q := λ(
              y,
              ∃(
                m,
                m ∈ S(n) /\ (app(h ↾ S(n))(m) === y) /\
                  z ∈ y
              )
            )
          )
      )

      val introM = thenHave(
        (function(h), n ∈ N, dom(h) === N) |-
          ∃(y, y ∈ range(h ↾ S(n)) /\ z ∈ y) <=> ∃(
            m,
            ∃(
              y,
              m ∈ S(n) /\ z ∈ y /\ (app(h ↾ S(n))(m) === y)
            )
          )
      ) by Tableau

      have(
        (∃(
          x,
          λ(y, m ∈ S(n) /\ z ∈ y)(x) /\
            (app(h ↾ S(n))(m) === x)
        )) <=> λ(y, m ∈ S(n) /\ z ∈ y)(app(h ↾ S(n))(m))
      ) by Tautology.from(
        onePointRule of
          (
            y := app(h ↾ S(n))(m),
            P := λ(y, m ∈ S(n) /\ z ∈ y)
          )
      )
      have(
        (∃(
          y,
          m ∈ S(n) /\ z ∈ y /\ (app(h ↾ S(n))(m) === y)
        )) <=> (m ∈ S(n) /\ z ∈ app(h ↾ S(n))(m))
      ) by Tautology.from(lastStep of (x := y), BetaReduction)
      val onePointExpanded = lastStep

      val domProof = have((n ∈ N, dom(h) === N, m ∈ S(n)) |- m ∈ dom(h)) subproof {
        assume(n ∈ N)
        assume(dom(h) === N)
        assume(m ∈ S(n))
        val succAsInter = have(S(n) === S(n) ∩ N) by Tautology.from(successorInterNat)
        have(m ∈ S(n)) by Hypothesis
        have(m ∈ (S(n) ∩ N)) by Congruence.from(lastStep, succAsInter)
        have(m ∈ N) by Tautology.from(
          lastStep,
          Intersection.membership of (z := m, x := S(n), y := N)
        )
        have(thesis) by Congruence.from(lastStep)
      }

      have(
        (function(h), n ∈ N, dom(h) === N, m ∈ S(n)) |-
          (∃(
            y,
            m ∈ S(n) /\ z ∈ y /\ (app(h ↾ S(n))(m) === y)
          )) <=> (m ∈ S(n) /\ z ∈ app(h)(m))
      ) by Congruence.from(
        Restriction.restrictedApp of (f := h, x := m, A := S(n)),
        domProof,
        onePointExpanded
      )
      thenHave(
        (function(h), n ∈ N, dom(h) === N) |-
          (∃(
            y,
            m ∈ S(n) /\ z ∈ y /\ (app(h ↾ S(n))(m) === y)
          )) <=> (m ∈ S(n) /\ z ∈ app(h)(m))
      ) by Tableau

      thenHave(
        (function(h), n ∈ N, dom(h) === N) |- ∀(
          m,
          (∃(
            y,
            m ∈ S(n) /\ z ∈ y /\ (app(h ↾ S(n))(m) === y)
          )) <=> (m ∈ S(n) /\ z ∈ app(h)(m))
        )
      ) by RightForall

      have(
        (function(h), n ∈ N, dom(h) === N) |- ∃(
          m,
          ∃(
            y,
            m ∈ S(n) /\ z ∈ y /\ (app(h ↾ S(n))(m) === y)
          )
        ) <=> ∃(m, m ∈ S(n) /\ z ∈ app(h)(m))
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of
          (
            P := λ(
              m,
              ∃(
                y,
                m ∈ S(n) /\ z ∈ y /\
                  (app(h ↾ S(n))(m) === y)
              )
            ),
            Q := λ(m, m ∈ S(n) /\ z ∈ app(h)(m))
          )
      )

      have(thesis) by Tautology.from(equivalenceRewriting, introM, lastStep)
    }

    val unionIsExists = have(
      (function(h), n ∈ N, dom(h) === N) |- z ∈ ⋃(range(
        h ↾ S(n)
      )) <=> ∃(m, m ∈ S(n) /\ z ∈ app(h)(m))
    ) by Tautology.from(
      rangeWitnessToSuccessorWitness,
      unionAxiom of (x := range(h ↾ S(n))),
      equivalenceRewriting of
        (
          p1 := z ∈ ⋃(range(h ↾ S(n))),
          p2 := ∃(y, y ∈ range(h ↾ S(n)) /\ z ∈ y),
          p3 := ∃(m, m ∈ S(n) /\ z ∈ app(h)(m))
        )
    )

    val cumulativeEquivalence = have(
      (cumulativeAssumption, n ∈ N) |- ∃(m, m ∈ S(n) /\ z ∈ app(h)(m)) <=> z ∈ app(h)(n)
    ) subproof {
      val toExists = {
        val seq1 = have(z ∈ app(h)(n) |- z ∈ app(h)(n)) by Hypothesis
        have(z ∈ app(h)(n) |- n ∈ S(n) /\ z ∈ app(h)(n)) by
          RightAnd(seq1, selfInSuccessor of (n := n))
        thenHave(z ∈ app(h)(n) |- ∃(m, m ∈ S(n) /\ z ∈ app(h)(m))) by RightExists
        thenHave((cumulativeAssumption, n ∈ N) |- z ∈ app(h)(n) ==> ∃(m, m ∈ S(n) /\ z ∈ app(h)(m))) by
          Weakening
      }

      val toValue = {
        have(cumulativeAssumption |- cumulativeAssumption) by Hypothesis
        val cumulativeAtM = thenHave(cumulativeAssumption |- m ∈ N ==> (m ⊆ n ==> app(h)(m) ⊆ app(h)(n))) by
          InstantiateForall(m)

        val succToSubset = have((n ∈ N, m ∈ S(n)) |- m ⊆ n) by Tautology.from(natSubset)

        val succIsNatStep = have(n ∈ N |- S(n) ∈ N) by Tautology.from(
          successorInOmega,
          equivalenceApply of (p1 := n ∈ N, p2 := S(n) ∈ N)
        )
        val succElemNat = have((n ∈ N, m ∈ S(n)) |- m ∈ N) by Tautology.from(
          succIsNatStep,
          omegaDownwardClosed of (x := m, y := S(n))
        )

        have(
          (cumulativeAssumption, n ∈ N, m ∈ S(n)) |- app(h)(m) ⊆ app(h)(n)
        ) by Tautology.from(cumulativeAtM, succElemNat, succToSubset)

        have(
          (cumulativeAssumption, n ∈ N, m ∈ S(n)) |- forall(z, z ∈ app(h)(m) ==> z ∈ app(h)(n))
        ) by Tautology.from(lastStep, subsetAxiom of (x := app(h)(m), y := app(h)(n)))
        thenHave((cumulativeAssumption, n ∈ N, m ∈ S(n) /\ z ∈ app(h)(m)) |- z ∈ app(h)(n)) by
          InstantiateForall(z)
        thenHave(
          (cumulativeAssumption, n ∈ N, ∃(m, m ∈ S(n) /\ z ∈ app(h)(m))) |- z ∈ app(h)(n)
        ) by LeftExists
        thenHave((cumulativeAssumption, n ∈ N) |- ∃(m, m ∈ S(n) /\ z ∈ app(h)(m)) ==> z ∈ app(h)(n)) by
          RightImplies
      }

      have(thesis) by RightIff(toValue, toExists)
    }

    have(
      (function(h), n ∈ N, dom(h) === N, cumulativeAssumption) |-
        (z ∈ ⋃(range(h ↾ S(n)))) <=> z ∈ app(h)(n)
    ) by Tautology.from(equivalenceRewriting, unionIsExists, cumulativeEquivalence)
    thenHave(
      (function(h), n ∈ N, dom(h) === N, cumulativeAssumption) |-
        ∀(z, z ∈ ⋃(range(h ↾ S(n))) <=> z ∈ app(h)(n))
    ) by RightForall

    have(thesis) by Tautology.from(
      equivalenceApply,
      lastStep,
      extensionalityAxiom of
        (x := ⋃(range(h ↾ S(n))), y := app(h)(n))
    )
    
  }

}
