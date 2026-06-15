package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.successor

/**
 * Backwards-compatibility facade. The integer / ω theory now lives in the
 * library at [[lisa.maths.SetTheory.Ordinals.Integer]], stated in terms of the
 * ordinal successor `S`.
 *
 * TEMPORARY: the ADT layer is phrased with the set-theoretic `successor`
 * (`x ∪ {x}`), so the lemmas whose statements mention the successor are
 * re-derived here in `successor`-form (bridged through `successor === S`), and
 * the remaining members are re-exported, with the former "Nat" names kept as
 * aliases.
 */
object ExtendedInteger extends lisa.Main {

  export lisa.maths.SetTheory.Ordinals.Integer.{
    emptyInOmega as zeroIsNat,
    omegaNotEmpty as natNotEmpty,
    omegaDownwardClosed as subsetIsNat,
    unionInOmega as unionOfTwoNats,
    existsInOmega as existsNat,
    successorInjectivity as _,
    zeroIsNotSucc as _,
    subsetSuccessor as _,
    subsetBelowSucc as _,
    succMembership as _,
    *
  }

  private val n, m, k = variable[Ind]
  private val x, α = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /** `successor` and the ordinal successor `S` denote the same set. */
  private val succEqS = Lemma(successor(n) === S(n)) {
    have(thesis) by Congruence.from(successor.definition of (x := n), S.definition of (α := n))
  }

  val nInSuccN = Theorem(n ∈ successor(n)) {
    have(thesis) by Congruence.from(Integer.selfInSuccessor of (n := n), succEqS)
  }

  val successorInjectivity = Theorem((n === m) <=> (successor(n) === successor(m))) {
    have(thesis) by Congruence.from(
      Integer.successorInjectivity of (n := n, m := m),
      succEqS,
      succEqS of (n := m)
    )
  }

  val zeroIsNotSucc = Theorem(!(successor(n) === ∅)) {
    have(thesis) by Congruence.from(Integer.zeroIsNotSucc of (n := n), succEqS)
  }

  val subsetSuccessor = Theorem(n ⊆ successor(n)) {
    have(thesis) by Congruence.from(Integer.subsetSuccessor of (n := n), succEqS)
  }

  val succMembership = Theorem((k ∈ successor(n)) <=> (k ∈ n) \/ (k === n)) {
    have(thesis) by Congruence.from(Integer.succMembership of (k := k, n := n), succEqS)
  }

  val successorIsNat = Theorem(n ∈ Integer.ω <=> successor(n) ∈ Integer.ω) {
    have(thesis) by Congruence.from(Integer.successorInOmega of (n := n), succEqS)
  }

  val subsetBelowSucc = Theorem(
    (m ∈ Integer.ω, n ∈ Integer.ω, m ⊆ successor(n)) |- (m === successor(n)) \/ (m ⊆ n)
  ) {
    have(thesis) by Congruence.from(Integer.subsetBelowSucc of (m := m, n := n), succEqS)
  }

  val natInduction = Theorem(
    (P(∅), ∀(m, m ∈ Integer.ω ==> (P(m) ==> P(successor(m))))) |-
      ∀(n, n ∈ Integer.ω ==> P(n))
  ) {
    val stepS = have(
      ∀(m, m ∈ Integer.ω ==> (P(m) ==> P(successor(m)))) |-
        ∀(m, m ∈ Integer.ω ==> (P(m) ==> P(S(m))))
    ) subproof {
      assume(∀(m, m ∈ Integer.ω ==> (P(m) ==> P(successor(m)))))
      thenHave(m ∈ Integer.ω ==> (P(m) ==> P(successor(m)))) by InstantiateForall(m)
      have(m ∈ Integer.ω ==> (P(m) ==> P(S(m)))) by Congruence.from(lastStep, succEqS of (n := m))
      thenHave(∀(m, m ∈ Integer.ω ==> (P(m) ==> P(S(m))))) by RightForall
    }
    have(thesis) by Tautology.from(Integer.omegaSuccessorInduction of (P := P, m := m, n := n), stepS)
  }
}
