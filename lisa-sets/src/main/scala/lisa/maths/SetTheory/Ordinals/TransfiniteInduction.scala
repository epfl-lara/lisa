package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Base.Predef.*

import lisa.maths.Quantifiers

import Ordinal.*

/**
 * This file is dedicated to proving the transfinite induction theorem, which
 * states that a theorem can be proved by induction along the ordinals.
 */
object TransfiniteInduction extends lisa.Main {

  private val x = variable[Ind]
  private val α, β, λ_ = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /**
   * Transfinite induction --- If `P(β)` for all `β < α` implies `P(α)` for any
   * `α`, then `P(α)` holds for any ordinal `α`.
   */
  val transfiniteInduction = Theorem(
    ∀(α, ordinal(α) ==> (∀(β, β ∈ α ==> P(β)) ==> P(α))) |- ∀(α, ordinal(α) ==> P(α))
  ) {
    assume(∀(α, ordinal(α) ==> (∀(β, β ∈ α ==> P(β)) ==> P(α))))
    thenHave(ordinal(α) ==> (∀(β, β ∈ α ==> P(β)) ==> P(α))) by InstantiateForall(α)
    thenHave((ordinal(α), ∀(β, β ∈ α ==> P(β))) |- P(α)) by Restate

    // Proof idea:
    // Towards a contradiction, suppose that there exists an ordinal that does
    // not satisfy `P`. Since Q = On \ P is a non-empty class of ordinals, it
    // admits a smallest element, call it α. Now, by minimality one has `P(β)`
    // for any `β ∈ α`, implying `P(α)` by assumption. Hence the contradiction.
    val αMinimal = ordinal(α) /\ ¬(P(α)) /\ ∀(β, β ∈ α ==> ¬(¬(P(β))))
    have(αMinimal |- ()) by Restate.from(lastStep)
    thenHave(∃(α, αMinimal) |- ()) by LeftExists

    // Thus the existence of any ordinal that does not satisfy `P` is a contradiction.
    have((ordinal(α), ¬(P(α))) |- ()) by Cut(
      Ordinal.ordinalClassMinimalElement of (P := λ(α, ¬(P(α)))),
      lastStep
    )
    thenHave(ordinal(α) ==> P(α)) by Restate
    thenHave(thesis) by RightForall
  }

  /**
   * Transfinite induction cases --- Breaks down [[transfiniteInduction]] into 3 cases:
   *
   *   - Zero case: `P(0)`
   *   - Successor case: `P(α) ==> P(α + 1)` for all ordinals `α`
   *   - Limit case: For any `λ` limit, if `P(β)` holds for any `β < λ`, then `P(λ)` holds
   */
  val transfiniteInductionCases = Theorem(
    (
      P(∅), // Zero case
      ∀(α, ordinal(α) /\ P(α) ==> P(S(α))), // Successor case
      ∀(λ_, limitOrdinal(λ_) ==> (∀(β, β ∈ λ_ ==> P(β)) ==> P(λ_))) // Limit case
    ) |-
      ∀(α, ordinal(α) ==> P(α))
  ) {
    // We show that for any ordinal `α`, if `∀β < α P(β)` then `P(α)` holds
    // by cases on `α` (zero, successor case, limit case). Then we can use
    // [[transfiniteInduction]] to conclude.

    assume(P(∅))
    val zeroCase = have(α === ∅ |- P(α)) by Congruence

    assume(∀(α, ordinal(α) /\ P(α) ==> P(S(α))))
    val succAssumption = thenHave(ordinal(β) /\ P(β) ==> P(S(β))) by InstantiateForall(β)

    val succCase = have((successorOrdinal(α), ∀(β, β ∈ α ==> P(β))) |- P(α)) subproof {
      assume(∀(β, β ∈ α ==> P(β)))
      thenHave(β ∈ α ==> P(β)) by InstantiateForall(β)
      thenHave(α === S(β) |- β ∈ S(β) ==> P(β)) by Congruence
      thenHave((ordinal(β), α === S(β)) |- P(S(β))) by Tautology.fromLastStep(
        Ordinal.lessThanSuccessor of (α := β),
        succAssumption
      )
      thenHave((ordinal(β), α === S(β)) |- P(α)) by Congruence
      thenHave(ordinal(β) /\ (α === S(β)) |- P(α)) by Restate
      thenHave(∃(β, ordinal(β) /\ (α === S(β))) |- P(α)) by LeftExists
      thenHave(thesis) by Substitute(successorOrdinal.definition)
    }

    assume(∀(λ_, limitOrdinal(λ_) ==> (∀(β, β ∈ λ_ ==> P(β)) ==> P(λ_))))
    thenHave(limitOrdinal(α) ==> (∀(β, β ∈ α ==> P(β)) ==> P(α))) by InstantiateForall(α)
    val limitCase = thenHave((limitOrdinal(α), ∀(β, β ∈ α ==> P(β))) |- P(α)) by Restate

    have(ordinal(α) ==> (∀(β, β ∈ α ==> P(β)) ==> P(α))) by Tautology.from(
      zeroCase,
      succCase,
      limitCase,
      Ordinal.ordinalClassification
    )
    thenHave(∀(α, ordinal(α) ==> (∀(β, β ∈ α ==> P(β)) ==> P(α)))) by RightForall

    have(thesis) by Cut(lastStep, transfiniteInduction)
  }
}
