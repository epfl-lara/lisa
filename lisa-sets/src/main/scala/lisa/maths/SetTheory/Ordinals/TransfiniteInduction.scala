package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Order.Predef._
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation._

import Ordinal._

/**
 * This file is dedicated to proving the transfinite induction theorem, which
 * states that a theorem can be proved by (strong) induction along the ordinals.
 */
object TransfiniteInduction extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val α, β, γ, δ, λ_ = variable[Ind]
  private val A = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /**
   * Theorem --- If `A` is a non-empty set of ordinals, then it admits a ∈-minimal element.
   *
   *   `∀α ∈ A. ordinal(α) /\ A ≠ ∅ ==> ∃α ∈ A. ∀β ∈ A. α <= β.
   */
  val setOfOrdinalsMinimalElement = Theorem(
    (A ⊆ ordinal, A ≠ ∅) |- ∃(α ∈ A, ∀(β ∈ A, α <= β))
  ) {
    assume(A ≠ ∅)

    // Since A ≠ ∅, take any α ∈ A.
    assume(A ⊆ ordinal)
    val `α ordinal` = thenHave(α ∈ A ==> ordinal(α)) by InstantiateForall(α)

    // If ∀β ∈ A, α <= β, we are done.
    val case1 =
      have((α ∈ A, ∀(β, β ∈ A ==> (α <= β))) |- α ∈ A /\ ∀(β ∈ A, α <= β)) by Restate
      thenHave((α ∈ A, ∀(β, β ∈ A ==> (α <= β))) |- ∃(α ∈ A, ∀(β ∈ A, α <= β))) by RightExists

    // If ∃β ∈ A, ¬(α <= β), then it means that β < α by [[comparability]]
    val case2 = have((α ∈ A, β ∈ A, ¬(α <= β)) |- ∃(α ∈ A, ∀(β ∈ A, α <= β))) subproof {
      assume(α ∈ A)
      assume(β ∈ A)
      assume(¬(α <= β))

      have(β < α) by Tautology.from(
        Ordinal.comparability,
        `α ordinal`,
        `α ordinal` of (α := β)
      )

      // Therefore A ∩ α ≠ ∅.
      val `A ∩ α ≠ ∅` = have((α ∈ A, β ∈ A, ¬(α <= β)) |- A ∩ α ≠ ∅) by Tautology.from(
        EmptySet.setWithElementNonEmpty of (x := β, y := (A ∩ α)),
        Intersection.membership of (z := β, x := A, y := α),
        lastStep
      )

      // Since α is well-ordered, we can take the ∈-minimal element of A ∩ α, call it δ.
      // It satisfies ∀β ∈ A. δ <= β
      have((δ ∈ (A ∩ α), minimal(δ)(A ∩ α)(membershipRelation(α))) |- ∀(β ∈ A, δ <= β)) subproof {
        assume(δ ∈ (A ∩ α))
        assume(minimal(δ)(A ∩ α)(membershipRelation(α)))

        /*
        val `δ is ordinal` = have(ordinal(δ)) by Tautology.from(
          Intersection.membership of (z := δ, x := A, y := α),
          Ordinal.elementOfOrdinal of (β := δ)
        )

        thenHave(∀(β, β ∈ (A ∩ α) ==> (β, δ) ∉ membershipRelation(α))) by Substitute(minimal.definition)
        thenHave(β ∈ (A ∩ α) ==> (β, δ) ∉ membershipRelation(α)) by InstantiateForall(β)
        thenHave(β ∈ (A ∩ α) ==> ¬((β ∈ α) /\ (δ ∈ α) /\ (β ∈ δ))) by Tautology.fromLastStep(MembershipRelation.membership of (x := β, y := δ, A := α))
        thenHave(β ∈ (A ∩ α) ==> ¬(β ∈ δ)) by Tautology.fromLastStep(
          Intersection.membership of (z := β, x := A, y := α),
          Intersection.membership of (z := δ, x := A, y := α)
        )
        thenHave(β ∈ (A ∩ α) ==> δ <= β) by Tautology.fromLastStep(
          Ordinal.comparability of (α := β, β := δ),
          Intersection.membership of (z := β, x := A, y := α),
          Ordinal.elementOfOrdinal of (β := δ)
        )
         */

        sorry
      }
      sorry
    }

    sorry
  }

  /**
   * Theorem --- If `P` is a non-empty class that has at least one ordinal, then
   * it admits a ∈-minimal ordinal.
   *
   *   `∃α ∈ On. P(α) ==> ∃α ∈ On. P(α) /\ ∀β < α. ¬P(β)`
   */
  val classOfOrdinalsMinimalElement = Theorem(
    (ordinal(α), P(α)) |- ∃(α, ordinal(α) /\ P(α) /\ ∀(β ∈ α, ¬(P(β))))
  ) {
    assume(ordinal(α))
    assume(P(α))

    // Consider the set `Q = {β ∈ α | P(β)}`
    val Q = { β ∈ α | P(β) }
    val `β ∈ Q` = have(β ∈ Q <=> (β ∈ α) /\ P(β)) by Comprehension.apply
    val `β is an ordinal` = thenHave(β ∈ Q |- ordinal(β)) by Tautology.fromLastStep(elementOfOrdinal)

    // If Q = ∅, `α` is minimal since there is no `β ∈ α` such that `P(β)` holds.
    val `case Q = ∅` = have(Q === ∅ |- ∃(α, ordinal(α) /\ P(α) /\ ∀(β ∈ α, ¬(P(β))))) subproof {
      assume(Q === ∅)

      have(β ∉ Q) by Congruence.from(EmptySet.definition of (x := β))
      thenHave(¬(β ∈ α /\ P(β))) by Substitute(`β ∈ Q`)
      thenHave(β ∈ α ==> ¬(P(β))) by Tautology
      thenHave(∀(β ∈ α, ¬(P(β)))) by RightForall
      thenHave(ordinal(α) /\ P(α) /\ ∀(β ∈ α, ¬(P(β)))) by Tautology
      thenHave(thesis) by RightExists
    }

    // If Q ≠ ∅, since `Q` is a set of ordinals it has a minimal element `β` that satisfies `P`.
    val `case Q ≠ ∅` = have(Q ≠ ∅ |- ∃(β, ordinal(β) /\ P(β) /\ ∀(x ∈ β, ¬(P(x))))) subproof {
      assume(Q ≠ ∅)

      // If `β ∈ S` is minimal, no element below it satisfy `P`.
      have((β ∈ Q, ∀(x ∈ Q, (β ∈ x) \/ (β === x))) |- ∀(x ∈ β, ¬(P(x)))) subproof {
        assume(β ∈ Q)

        val minimality = assume(∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x)))

        val `x is an ordinal` = have(x ∈ β |- ordinal(x)) by Tautology.from(
          `β is an ordinal`,
          elementOfOrdinal of (α := β, β := x)
        )
        thenHave(x ∈ β ==> x ∈ α) by Tautology.fromLastStep(
          `β ∈ Q`,
          transitivity of (α := x, β := β, γ := α)
        )

        // Let x ∈ β. If x ∉ Q then ¬P(x) by comprehension.
        val `x ∉ Q` = have((x ∈ β, x ∉ Q) |- ¬(P(x))) by Tautology.from(`β ∈ Q` of (β := x), lastStep)

        // If x ∈ Q then by minimality either β ∈ x or β === x, and both cases lead to self-inclusion
        val `x ∈ Q` = have((x ∈ β, x ∈ Q) |- ¬(P(x))) subproof {
          have(x ∈ Q ==> (β ∈ x) \/ (β === x)) by InstantiateForall(x)(minimality)
          val cases = thenHave(x ∈ Q |- (β ∈ x) \/ (β === x)) by Restate

          assume(x ∈ β)
          assume(x ∈ Q)

          val `case β ∈ x` = have(β ∈ x |- ()) by Tautology.from(
            `x is an ordinal`,
            `β is an ordinal`,
            transitivity of (α := β, β := x, γ := β),
            FoundationAxiom.selfNonInclusion of (x := β)
          )

          val `case β = x` = {
            have(β === x |- β ∈ β) by Congruence
            thenHave(β === x |- ()) by Tautology.fromLastStep(FoundationAxiom.selfNonInclusion of (x := β))
          }

          have(thesis) by Tautology.from(cases, `case β ∈ x`, `case β = x`)
        }

        have(x ∈ β ==> ¬(P(x))) by Tautology.from(`x ∉ Q`, `x ∈ Q`)
        thenHave(thesis) by RightForall
      }
      thenHave((β ∈ Q) /\ ∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x)) |- ordinal(β) /\ P(β) /\ ∀(x, x ∈ β ==> ¬(P(x)))) by Tautology.fromLastStep(`β ∈ Q`, `β is an ordinal`)
      thenHave((β ∈ Q) /\ ∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x)) |- ∃(β, ordinal(β) /\ P(β) /\ ∀(x, x ∈ β ==> ¬(P(x))))) by RightExists
      val conclusion = thenHave(∃(β ∈ Q, ∀(x ∈ Q, (β ∈ x) \/ (β === x))) |- ∃(β, ordinal(β) /\ P(β) /\ ∀(x, x ∈ β ==> ¬(P(x))))) by LeftExists

      // We show that `Q` is a non-empty set of ordinals to satisfy the assumptions of [[setOfOrdinalsMinimalElement]]
      have(β ∈ Q ==> ordinal(β)) by Tautology.from(
        `β ∈ Q`,
        elementOfOrdinal
      )
      thenHave(∀(β ∈ Q, ordinal(β))) by RightForall

      have(thesis) by Tautology.from(
        lastStep,
        setOfOrdinalsMinimalElement of (A := Q),
        conclusion
      )
    }

    have(thesis) by Tautology.from(`case Q = ∅`, `case Q ≠ ∅`)
  }

  /**
   * Transfinite induction --- If `P(β)` for all `β < α` implies `P(α)` for any
   * `α`, then `P(α)` holds for any ordinal `α`.
   */
  val transfiniteInduction = Theorem(
    ∀(α, ordinal(α) ==> (∀(β ∈ α, P(β)) ==> P(α))) |- ∀(α, ordinal(α) ==> P(α))
  ) {
    assume(∀(α, ordinal(α) ==> (∀(β ∈ α, P(β)) ==> P(α))))
    thenHave(ordinal(α) ==> (∀(β ∈ α, P(β)) ==> P(α))) by InstantiateForall(α)
    val IHα = thenHave((ordinal(α), ∀(β ∈ α, P(β))) |- P(α)) by Restate

    // Proof idea:
    // Towards a contradiction, suppose that there exists an ordinal that does
    // not satisfy `P`. Since Q = On \ P is a non-empty class of ordinals, it
    // admits a smallest element, call it α. Now, by minimality one has `P(β)`
    // for any `β ∈ α`, implying `P(α)` by assumption. Hence the contradiction.
    val αMinimal = ordinal(α) /\ ¬(P(α)) /\ ∀(β ∈ α, P(β))
    have(αMinimal |- ()) by Restate.from(IHα)
    thenHave(∃(α, αMinimal) |- ()) by LeftExists

    // Thus the existence of any ordinal that does not satisfy `P` is a contradiction.
    have((ordinal(α), ¬(P(α))) |- ()) by Cut(
      classOfOrdinalsMinimalElement of (P := λ(α, ¬(P(α)))),
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
      ∀(λ_, limitOrdinal(λ_) ==> (∀(β ∈ λ_, P(β)) ==> P(λ_))) // Limit case
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

    val succCase = have((successorOrdinal(α), ∀(β ∈ α, P(β))) |- P(α)) subproof {
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

    assume(∀(λ_, limitOrdinal(λ_) ==> (∀(β ∈ λ_, P(β)) ==> P(λ_))))
    thenHave(limitOrdinal(α) ==> (∀(β ∈ α, P(β)) ==> P(α))) by InstantiateForall(α)
    val limitCase = thenHave((limitOrdinal(α), ∀(β ∈ α, P(β))) |- P(α)) by Restate

    have(ordinal(α) ==> (∀(β ∈ α, P(β)) ==> P(α))) by Tautology.from(
      zeroCase,
      succCase,
      limitCase,
      Ordinal.ordinalClassification
    )
    thenHave(∀(α, ordinal(α) ==> (∀(β ∈ α, P(β)) ==> P(α)))) by RightForall

    have(thesis) by Cut(lastStep, transfiniteInduction)
  }
}
