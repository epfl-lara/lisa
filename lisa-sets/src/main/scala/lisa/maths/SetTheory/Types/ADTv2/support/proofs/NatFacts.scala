package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Base.FoundationAxiom
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Ordinals.Ordinal
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinal
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.omegaOrdinal
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.natInduction
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.successorIsNat
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.zeroIsNotSucc

object NatFacts {

  private val Pred = variable[Ind >>: Prop]

  val NatMem = MembershipRelation.membershipRelation(N)

  val succIntro = Theorem(n ∈ N |- successor(n) ∈ N) {
    assume(n ∈ N)
    have(thesis) by Tautology.from(successorIsNat of (n := n))
  }

  val induction = Theorem(
    (Pred(∅), ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(successor(n))))) |-
      ∀(n, (n ∈ N) ==> Pred(n))
  ) {
    val H0 = Pred(∅)
    val Hstep = ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(successor(n))))

    val baseAtEmpty = have((H0, Hstep) |- Pred(∅)) subproof {
      have(thesis) by Hypothesis
    }

    val stepAtSucc =
      have((H0, Hstep) |- ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(successor(n))))) subproof {
        val hypStep = have((H0, Hstep) |- Hstep) by Hypothesis
        val stepAtN = have((H0, Hstep) |- (n ∈ N) ==> (Pred(n) ==> Pred(successor(n)))) by
          InstantiateForall(n)(hypStep)
        have((H0, Hstep) |- (n ∈ N) ==> (Pred(n) ==> Pred(successor(n)))) subproof {
          assume(n ∈ N)
          assume(Pred(n))
          have((H0, Hstep, n ∈ N, Pred(n)) |- Pred(successor(n))) by Restate.from(stepAtN)
        }
        thenHave(thesis) by RightForall
      }

    have((H0, Hstep) |- ∀(n, (n ∈ N) ==> Pred(n))) by Tautology
      .from(natInduction of (P := Pred), baseAtEmpty, stepAtSucc)
    thenHave(thesis) by Restate
  }

  val succMembership = Theorem((k ∈ successor(n)) <=> (k ∈ n) \/ (k === n)) {
    val memSucc = have(k ∈ successor(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
      have(k ∈ successor(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
        have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by
          Congruence.from(successor.definition of (x := n)),
        have(
          k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))
        ) by
          Tautology
            .from(Union.membership of (x := n, y := Singleton.singleton(n), z := k)),
        have(k ∈ Singleton.singleton(n) <=> (k === n)) by
          Tautology.from(Singleton.membership of (x := n, y := k))
      )
    )
    have(thesis) by Restate.from(memSucc)
  }

  val nInSucc = Theorem(n ∈ successor(n)) {
    val mem = have(n ∈ successor(n) <=> (n ∈ n) \/ (n === n)) by
      Restate.from(succMembership of (k := n, n := n))
    val refl = have(n === n) by Restate
    have(thesis) by Tautology.from(mem, refl)
  }

  val succInjective = Theorem(successor(n) === successor(m) |- n === m) {
    assume(successor(n) === successor(m))

    val nInSm = have(n ∈ successor(m)) by
      Congruence.from(NatFacts.nInSucc.of(n := n))
    val nCase = have(n ∈ m \/ (n === m)) by
      Tautology.from(NatFacts.succMembership.of(k := n, n := m), nInSm)
    val mInSn = have(m ∈ successor(n)) by
      Congruence.from(NatFacts.nInSucc.of(n := m))
    val mCase = have(m ∈ n \/ (m === n)) by
      Tautology.from(NatFacts.succMembership.of(k := m, n := n), mInSn)

    val fromNInM = have(n ∈ m |- n === m) subproof {
      assume(n ∈ m)
      val notMInN = have(¬(m ∈ n)) by Tautology.from(
        FoundationAxiom.membershipAsymmetric of (x := n, y := m),
        have(n ∈ m) by Tautology
      )
      val mEqN = have(m === n) by Tautology.from(mCase, notMInN)
      have(thesis) by Congruence.from(mEqN)
    }

    val fromNEqM = have(n === m |- n === m) by Restate
    have(thesis) by Tautology.from(nCase, fromNInM, fromNEqM)
  }

  val elementsTransitive = Theorem((n ∈ N) |- TransitiveSet.transitiveSet(n)) {
    val ordN = have(n ∈ N |- ordinal(n)) by Restate.from(omegaOrdinal of (α := n))
    have(thesis) by Tautology.from(ordN, ordinal.definition of (α := n))
  }

  val succNeZero = Lemma((n ∈ N) |- (successor(n) =/= ∅)) {
    assume(n ∈ N)
    have(thesis) by Tautology.from(zeroIsNotSucc of (n := n))
  }

  val comparability = Theorem((m ∈ N, n ∈ N) |- (m === n) \/ (m ∈ n) \/ (n ∈ m)) {
    val mOrd = have(m ∈ N |- ordinal(m)) by Restate.from(omegaOrdinal of (α := m))
    val nOrd = have(n ∈ N |- ordinal(n)) by Restate.from(omegaOrdinal of (α := n))
    have(thesis) by Tautology.from(mOrd, nOrd, Ordinal.comparability of (α := m, β := n))
  }

  val subsetBelowSucc = Theorem((m ∈ N, n ∈ N, m ⊆ successor(n)) |- (m === successor(n)) \/ (m ⊆ n)) {
    val mInN = assume(m ∈ N)
    val nInN = assume(n ∈ N)
    val mSubSn = assume(m ⊆ successor(n))

    val SnInN = have(successor(n) ∈ N) by
      Tautology.from(nInN, succIntro.of(n := n))

    val cmp = have(
      (m === successor(n)) \/ (m ∈ successor(n)) \/ (successor(n) ∈ m)
    ) by Tautology.from(
      mInN,
      SnInN,
      comparability of (m := m, n := successor(n))
    )

    val caseEq = have(
      m === successor(n) |- (m === successor(n)) \/ (m ⊆ n)
    ) by Tautology

    val caseIn = have(
      m ∈ successor(n) |- (m === successor(n)) \/ (m ⊆ n)
    ) subproof {
      val mInSn = assume(m ∈ successor(n))
      val split = have((m ∈ n) \/ (m === n)) by Tautology.from(
        mInSn,
        succMembership.of(k := m, n := n)
      )

      val fromIn = have(m ∈ n |- m ⊆ n) subproof {
        val mInNCase = assume(m ∈ n)
        val nTrans = have(TransitiveSet.transitiveSet(n)) by
          Tautology.from(nInN, elementsTransitive.of(n := n))
        have(m ⊆ n) by Tautology.from(
          mInNCase,
          nTrans,
          TransitiveSet.elementIsSubset.of(A := n, x := m)
        )
      }

      val fromEq = have(m === n |- m ⊆ n) by
        Congruence.from(Subset.reflexivity of (x := n))

      have(m ⊆ n) by Tautology.from(split, fromIn, fromEq)
      thenHave(thesis) by Tautology
    }

    val caseGt = have(
      successor(n) ∈ m |- (m === successor(n)) \/ (m ⊆ n)
    ) subproof {
      val SnInM = assume(successor(n) ∈ m)
      val SnInSn = have(successor(n) ∈ successor(n)) by Tautology.from(
        mSubSn,
        SnInM,
        Subset.membership of (x := m, y := successor(n), z := successor(n))
      )
      have(thesis) by Tautology.from(
        SnInSn,
        FoundationAxiom.selfNonInclusion of (x := successor(n))
      )
    }

    have(thesis) by Tautology.from(cmp, caseEq, caseIn, caseGt)
  }

}
