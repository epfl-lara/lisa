package lisa.maths.SetTheory.Types.ADT.height.proofs

import lisa.maths.SetTheory.Base.Intersection.∩
import lisa.maths.SetTheory.Base._
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Functions.UnionRange.unionRangeMembership
import lisa.maths.SetTheory.Ordinals.Integer.elementsTransitive
import lisa.maths.SetTheory.Ordinals.Integer.selfInSuccessor
import lisa.maths.SetTheory.Ordinals.Integer.succMembership
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._

/**
 * Collapses the union of a monotone height sequence through its last stage.
 */
object UnionRangeCollapse {

  private val natSubset = Lemma((n ∈ N, m ∈ S(n)) |- m ⊆ n) {
    val memberCase = have((n ∈ N, m ∈ n) |- m ⊆ n) by
      Tautology.from(elementsTransitive, TransitiveSet.elementIsSubset of (x := m, A := n))
    val equalCase = have(m === n |- m ⊆ n) by Congruence.from(Subset.reflexivity of (x := n))
    have(thesis) by Tautology.from(memberCase, equalCase, succMembership of (k := m))
  }

  /**
   * A monotone sequence on ω contains every earlier value in its last value.
   */
  val unionRangeCollapse = Lemma(
    (
      function(h),
      dom(h) === N,
      n ∈ N,
      forall(m, m ∈ N ==> (m ⊆ n ==> app(h)(m) ⊆ app(h)(n)))
    ) |- ⋃(range(h ↾ S(n))) === app(h)(n)
  ) {
    val hFunction = assume(function(h))
    assume(dom(h) === N)
    assume(n ∈ N)
    val cumulative = assume(∀(m, m ∈ N ==> (m ⊆ n ==> app(h)(m) ⊆ app(h)(n))))
    val restricted = h ↾ S(n)
    val witness = m ∈ dom(restricted) /\ z ∈ app(restricted)(m)

    val restrictedFunction = have(function(restricted)) by
      Tautology.from(hFunction, Restriction.isFunction of (f := h, A := S(n)))
    val unionMembership = have(z ∈ ⋃(range(restricted)) <=> ∃(m, witness)) by
      Tautology.from(restrictedFunction, unionRangeMembership of (h := restricted, n := m))
    val restrictedDomain = have(dom(restricted) === N ∩ S(n)) by
      Congruence.from(Restriction.domain of (f := h, A := S(n)))
    val domainMembership = have(m ∈ dom(restricted) <=> (m ∈ N /\ m ∈ S(n))) by
      Congruence.from(restrictedDomain, Intersection.membership of (z := m, x := N, y := S(n)))

    val witnessToValue = have(witness |- z ∈ app(h)(n)) subproof {
      assume(witness)
      val mInNat = have(m ∈ N) by Tautology.from(domainMembership)
      val mInSuccessor = have(m ∈ S(n)) by Tautology.from(domainMembership)
      val mInDomain = have(m ∈ dom(h)) by Congruence.from(mInNat)
      val restrictedValue = have(app(restricted)(m) === app(h)(m)) by Tautology.from(
        Restriction.restrictedApp of (f := h, x := m, A := S(n)),
        hFunction,
        mInDomain,
        mInSuccessor
      )
      val zInRestrictedValue = have(z ∈ app(restricted)(m)) by Tautology
      val zInValue = have(z ∈ app(h)(m)) by Congruence.from(restrictedValue, zInRestrictedValue)
      val cumulativeAtM = have(m ∈ N ==> (m ⊆ n ==> app(h)(m) ⊆ app(h)(n))) by InstantiateForall(m)(cumulative)
      have(app(h)(m) ⊆ app(h)(n)) by Tautology.from(cumulativeAtM, natSubset, mInNat, mInSuccessor)
      have(thesis) by Tautology.from(
        lastStep,
        zInValue,
        Subset.membership of (x := app(h)(m), y := app(h)(n), z := z)
      )
    }
    val fromExists = have(∃(m, witness) |- z ∈ app(h)(n)) by LeftExists(witnessToValue)
    val forward = have(z ∈ ⋃(range(restricted)) |- z ∈ app(h)(n)) by Tautology.from(unionMembership, fromExists)

    val backward = have(z ∈ app(h)(n) |- z ∈ ⋃(range(restricted))) subproof {
      assume(z ∈ app(h)(n))
      val nInDomain = have(n ∈ dom(h)) by Congruence
      val nInRestrictedDomain = have(n ∈ dom(restricted)) by
        Tautology.from(domainMembership of (m := n), selfInSuccessor)
      val restrictedValue = have(app(restricted)(n) === app(h)(n)) by Tautology.from(
        Restriction.restrictedApp of (f := h, x := n, A := S(n)),
        hFunction,
        nInDomain,
        selfInSuccessor
      )
      have(z ∈ app(restricted)(n)) by Congruence.from(restrictedValue)
      thenHave(n ∈ dom(restricted) /\ z ∈ app(restricted)(n)) by Tautology.fromLastStep(nInRestrictedDomain)
      thenHave(∃(m, witness)) by RightExists
      have(thesis) by Tautology.from(lastStep, unionMembership)
    }

    have(z ∈ ⋃(range(restricted)) <=> z ∈ app(h)(n)) by Tautology.from(forward, backward)
    thenHave(thesis) by Extensionality
  }
}
