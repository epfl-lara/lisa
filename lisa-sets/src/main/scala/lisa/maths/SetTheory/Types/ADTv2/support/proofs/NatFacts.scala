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

  val Zero = DEF(∅)
  val Succ = DEF(λ(x, successor(x)))
  val NatMem = MembershipRelation.membershipRelation(N)


  val succIntro = Theorem(n ∈ N |- Succ(n) ∈ N) {
    assume(n ∈ N)
    val succInNat = have(successor(n) ∈ N) by Tautology.from(successorIsNat of (n := n))
    val succEq = have(Succ(n) === successor(n)) by Tautology
      .from(Succ.definition of (x := n))
    have(thesis) by Congruence.from(succInNat, succEq)
  }

  val induction = Theorem(
    (Pred(Zero), ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(Succ(n))))) |-
      ∀(n, (n ∈ N) ==> Pred(n))
  ) {
    val H0 = Pred(Zero)
    val Hstep = ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(Succ(n))))

    val baseAtEmpty = have((H0, Hstep) |- Pred(∅)) subproof {
      val hyp0 = have((H0, Hstep) |- H0) by Hypothesis
      val zeroEq = have(Zero === ∅) by Tautology.from(Zero.definition)
      have(thesis) by Congruence.from(hyp0, zeroEq)
    }

    val stepAtSucc =
      have((H0, Hstep) |- ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(successor(n))))) subproof {
        val hypStep = have((H0, Hstep) |- Hstep) by Hypothesis
        val stepAtN = have((H0, Hstep) |- (n ∈ N) ==> (Pred(n) ==> Pred(Succ(n)))) by
          InstantiateForall(n)(hypStep)
        have((H0, Hstep) |- (n ∈ N) ==> (Pred(n) ==> Pred(successor(n)))) subproof {
          assume(n ∈ N)
          assume(Pred(n))
          val predSucc = have((H0, Hstep, n ∈ N, Pred(n)) |- Pred(Succ(n))) by
            Tautology.from(stepAtN)
          val succEq = have(Succ(n) === successor(n)) by Tautology
            .from(Succ.definition of (x := n))
          have((H0, Hstep, n ∈ N, Pred(n)) |- Pred(successor(n))) by
            Congruence.from(predSucc, succEq)
        }
        thenHave(thesis) by RightForall
      }

    have((H0, Hstep) |- ∀(n, (n ∈ N) ==> Pred(n))) by Tautology
      .from(natInduction of (P := Pred), baseAtEmpty, stepAtSucc)
    thenHave(thesis) by Restate
  }

  val succMembership = Theorem((k ∈ Succ(n)) <=> (k ∈ n) \/ (k === n)) {
    val succDef = have(Succ(n) === successor(n)) by
      Tautology.from(Succ.definition of (x := n))
    val memSucc = have(k ∈ Succ(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
      have(k ∈ Succ(n) <=> k ∈ successor(n)) by Congruence.from(succDef),
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

  val nInSucc = Theorem(n ∈ Succ(n)) {
    val mem = have(n ∈ Succ(n) <=> (n ∈ n) \/ (n === n)) by
      Restate.from(succMembership of (k := n, n := n))
    val refl = have(n === n) by Restate
    have(thesis) by Tautology.from(mem, refl)
  }

  val succInjective = Theorem(Succ(n) === Succ(m) |- n === m) {
    assume(Succ(n) === Succ(m))

    val nInSm = have(n ∈ Succ(m)) by
      Congruence.from(NatFacts.nInSucc.of(n := n))
    val nCase = have(n ∈ m \/ (n === m)) by
      Tautology.from(NatFacts.succMembership.of(k := n, n := m), nInSm)
    val mInSn = have(m ∈ Succ(n)) by
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

  val succNeZero = Lemma((n ∈ N) |- (Succ(n) =/= Zero)) {
    assume(n ∈ N)
    val succNeEmpty = have(Succ(n) =/= ∅) by Congruence
      .from(zeroIsNotSucc of (n := n), Succ.definition of (x := n))
    val zeroEq = have(Zero === ∅) by Tautology.from(Zero.definition)
    have(thesis) by Congruence.from(succNeEmpty, zeroEq)
  }

  val comparability = Theorem((m ∈ N, n ∈ N) |- (m === n) \/ (m ∈ n) \/ (n ∈ m)) {
    val mOrd = have(m ∈ N |- ordinal(m)) by Restate.from(omegaOrdinal of (α := m))
    val nOrd = have(n ∈ N |- ordinal(n)) by Restate.from(omegaOrdinal of (α := n))
    have(thesis) by Tautology.from(mOrd, nOrd, Ordinal.comparability of (α := m, β := n))
  }

  val subsetBelowSucc = Theorem((m ∈ N, n ∈ N, m ⊆ Succ(n)) |- (m === Succ(n)) \/ (m ⊆ n)) {
    val mInN = assume(m ∈ N)
    val nInN = assume(n ∈ N)
    val mSubSn = assume(m ⊆ Succ(n))

    val SnInN = have(Succ(n) ∈ N) by
      Tautology.from(nInN, succIntro.of(n := n))

    val cmp = have(
      (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)
    ) by Tautology.from(
      mInN,
      SnInN,
      comparability of (m := m, n := Succ(n))
    )

    val caseEq = have(
      m === Succ(n) |- (m === Succ(n)) \/ (m ⊆ n)
    ) by Tautology

    val caseIn = have(
      m ∈ Succ(n) |- (m === Succ(n)) \/ (m ⊆ n)
    ) subproof {
      val mInSn = assume(m ∈ Succ(n))
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
      Succ(n) ∈ m |- (m === Succ(n)) \/ (m ⊆ n)
    ) subproof {
      val SnInM = assume(Succ(n) ∈ m)
      val SnInSn = have(Succ(n) ∈ Succ(n)) by Tautology.from(
        mSubSn,
        SnInM,
        Subset.membership of (x := m, y := Succ(n), z := Succ(n))
      )
      have(thesis) by Tautology.from(
        SnInSn,
        FoundationAxiom.selfNonInclusion of (x := Succ(n))
      )
    }

    have(thesis) by Tautology.from(cmp, caseEq, caseIn, caseGt)
  }

}
