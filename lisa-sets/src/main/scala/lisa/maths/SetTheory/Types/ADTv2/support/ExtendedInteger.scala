package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.Ordinals.Ordinal
import lisa.maths.SetTheory.Ordinals.Ordinal.{<, <=, successorOrdinal, ordinal, S, limitOrdinal}
import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Ordinals.TransfiniteInduction.transfiniteInductionCases
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.EmptySet
import lisa.utils.prooflib.BasicStepTactic.LeftForall
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall
import lisa.utils.prooflib.SimpleDeducedSteps.Generalize
import lisa.utils.prooflib.SimpleDeducedSteps.Generalize

/**
 * This file defines integers as ordinals whose elements are either zero
 * or successor ordinals.
 *
 * `ω` is defined as the set of all integers, and is itself an ordinal which
 * is limit.
 */
object ExtendedInteger extends lisa.Main {

  private val x = variable[Ind]
  private val α, β = variable[Ind]
  private val y, z = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /**
   * Definition --- An ordinal `α` is an integer if and only if all its predecessors are zero or successors.
   */
  val integer = Integer.integer

  /**
   * Definition --- The set of all integers is the set denoted `ω`.
   *
   * Its existence is guaranteed by the [[infinityAxiom]].
   */
  val ω = Integer.ω

  /**
   * Bridge theorem --- Characterization of membership in `ω` by `integer`.
   */
  val omegaCharacterization = Axiom(
    ∀(α, α ∈ ω <=> integer(α))
  )

  private val γ, λ_ = variable[Ind]

  private val zeroIsInteger = Theorem(
    integer(∅)
  ) {
    have(β <= ∅ |- (β ∈ ∅) \/ (β === ∅)) by Tautology
    have(β ∈ ∅ |- ()) by Tautology.from(EmptySet.definition of (x := β))
    have(β <= ∅ |- β === ∅) by Tautology.from(lastStep, lastStep)
    thenHave((β <= ∅) ==> (β === ∅) \/ successorOrdinal(β)) by Tautology
    thenHave(∀(β, (β <= ∅) ==> (β === ∅) \/ successorOrdinal(β))) by RightForall
    thenHave(thesis) by Substitute(integer.definition of (α := ∅))
  }

  val integerIsOrdinal = Theorem(
    integer(α) |- ordinal(α)
  ) {
    assume(integer(α))
    thenHave(∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))) by
      Substitute(integer.definition)
    thenHave((α <= α) ==> (α === ∅) \/ successorOrdinal(α)) by InstantiateForall(α)
    have((α === ∅) \/ successorOrdinal(α)) by Tautology.from(lastStep)

    val zeroCase = have(α === ∅ |- ordinal(α)) by Congruence.from(Ordinal.zeroOrdinal)

    val succCase = have(successorOrdinal(α) |- ordinal(α)) subproof {
      assume(successorOrdinal(α))
      thenHave(∃(γ, ordinal(γ) /\ (α === S(γ)))) by Substitute(successorOrdinal.definition)
      have( (α === S(γ)) |- ordinal(γ) ==> ordinal(S(γ))) by Tautology.from(
        Ordinal.sucessorIsOrdinal of (α := γ)
      )
      have( α === S(γ) |- ordinal(γ) ==>  ordinal(α)) by Congruence.from(lastStep)
      thenHave(ordinal(γ) /\ (α === S(γ)) |- ordinal(α)) by Tautology
      thenHave(∃(γ, ordinal(γ) /\ (α === S(γ))) |- ordinal(α)) by LeftExists

      have(thesis) by Sorry
    }

    have(thesis) by LeftOr(zeroCase, succCase)
  }

  private val integerSuccessor = Theorem(
    integer(α) |- integer(S(α))
  ) {
    assume(integer(α))

    have(β <= S(α) |- (β ∈ α) \/ (β === α) \/ (β === S(α))) subproof {
      assume(β <= S(α))
      thenHave(β ∈ S(α) \/ (β === S(α))) by Tautology
      thenHave(β ∈ Union.∪(α)(Singleton.singleton(α)) \/ (β === S(α))) by Substitute(S.definition)
      have(β ∈ Union.∪(α)(Singleton.singleton(α)) ==> (β ∈ α) \/ (β === α)) by Tautology.from(
        Union.membership of (x := α, y := Singleton.singleton(α), z := β),
        Singleton.membership of (x := α, y := β)
      )
      have(thesis) by Sorry //.from(lastStep)
    }

    // val inAlphaCase = have(β ∈ α |- (β === ∅) \/ successorOrdinal(β)) by Tautology.from(
    //   integer.definition of (α := α)
    // )

    // val eqAlphaCase = have((β === α) |- (β === ∅) \/ successorOrdinal(β)) by Congruence.from(
    //   {
    //     have((α === ∅) \/ successorOrdinal(α)) by Tautology.from(
    //       integer.definition of (α := α),
    //       integerIsOrdinal,
    //       Ordinal.ordinalClassification
    //     )
    //     lastStep
    //   }
    // )

    // val eqSuccCase = have((β === S(α)) |- (β === ∅) \/ successorOrdinal(β)) subproof {
    //   assume(β === S(α))
    //   have(ordinal(α)) by Tautology.from(integerIsOrdinal)
    //   have(successorOrdinal(S(α))) by Tautology.from(
    //     successorOrdinal.definition of (α := S(α), β := α)
    //   )
    //   thenHave((β === S(α)) |- successorOrdinal(β)) by Congruence
    //   have(thesis) by Tautology.from(lastStep)
    // }

    // have(β <= S(α) |- (β === ∅) \/ successorOrdinal(β)) by Tautology.from(
    //   lastStep,
    //   inAlphaCase,
    //   eqAlphaCase,
    //   eqSuccCase
    // )
    // thenHave(∀(β, β <= S(α) ==> (β === ∅) \/ successorOrdinal(β))) by RightForall
    // thenHave(thesis) by Substitute(integer.definition of (α := S(α)))
    thenHave(thesis) by Sorry
  }

  private val integerPredecessor = Theorem(
    integer(S(α)) |- integer(α)
  ) {
    assume(integer(S(α)))

    val alphaInSucc = have(α ∈ S(α)) subproof {
      have(α ∈ Singleton.singleton(α)) by Tautology.from(
        Singleton.membership of (x := α, y := α),
      )
      have(α ∈ Union.∪(α)(Singleton.singleton(α))) by Tautology.from(lastStep,
        Union.membership of (x := α, y := Singleton.singleton(α), z := α)
      )
      have(thesis) by Congruence.from(lastStep,S.definition)
    }


    have(β <= α |- α <= S(α)) by Tautology.from(alphaInSucc)
    // have(β <= α |- β <= S(α)) by Tautology.from(lastStep, Ordinal.transitivity)
    // have(β <= S(α) |- (β === ∅) \/ successorOrdinal(β)) by Tautology.from(
    //   integer.definition of (α := S(α))
    // )
    // have(β <= α |- (β === ∅) \/ successorOrdinal(β)) by Cut(lastStep, lastStep)
    // thenHave(∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))) by RightForall
    thenHave(thesis) by Sorry // Substitute(integer.definition)
  }

  private val omegaOrdinal = Theorem(
    α ∈ ω |- ordinal(α)
  ) {
    have(α ∈ ω |- integer(α)) by InstantiateForall(α)(omegaCharacterization)
    have(thesis) by Tautology.from(lastStep, integerIsOrdinal)
  }

  /**
   * Bridge theorem --- Successor closure of `ω`.
   */
  val omegaSuccessor = Theorem(
    α ∈ ω |- S(α) ∈ ω
  ) {
    have(α ∈ ω |- integer(α)) by InstantiateForall(α)(omegaCharacterization)
    val st1 = have(α ∈ ω |- integer(S(α))) by Tautology.from(lastStep, integerSuccessor)
    have(integer(S(α)) |- S(α) ∈ ω) by InstantiateForall(S(α))(omegaCharacterization)
    have(thesis) by Tautology.from(lastStep, st1)
  }

  /**
   * Bridge theorem --- Predecessor closure of `ω` for successors.
   */
  val omegaPredecessor = Theorem(
    S(α) ∈ ω |- α ∈ ω
  ) {
    have(S(α) ∈ ω |- integer(S(α))) by InstantiateForall(S(α))(omegaCharacterization)
    val st1 = have(S(α) ∈ ω |- integer(α)) by Tautology.from(lastStep, integerPredecessor)
    have(integer(α) |- α ∈ ω) by InstantiateForall(α)(omegaCharacterization)
    have(thesis) by Tautology.from(lastStep, st1)
  }

  /**
   * Bridge theorem --- Induction on `ω` with successor `S`.
   */
  val omegaInduction = Theorem(
    (P(∅), ∀(α, α ∈ ω ==> (P(α) ==> P(S(α))))) |- ∀(α, α ∈ ω ==> P(α))
  ) {
    def Q(t: Expr[Ind]): Expr[Prop] = t ∈ ω ==> P(t)

    val qZero = have(Q(∅)) subproof {
      // have(integer(∅) |- ∅ ∈ ω) by InstantiateForall(∅)(omegaCharacterization)
      // have(∅ ∈ ω) by Tautology.from(lastStep, zeroIsInteger)
      // have(∅ ∈ ω /\ P(∅)) by Tautology.from(lastStep)
      have(Q(∅)) by Sorry
    }

    val qSucc = have(∀(α, ordinal(α) /\ Q(α) ==> Q(S(α)))) subproof {
      val hyp = ordinal(α) /\ Q(α)
      // assume(ordinal(α) /\ Q(α))
      have(hyp |- Q(α)) by Tautology

      have(S(α) ∈ ω |- α ∈ ω) by Tautology.from(omegaPredecessor)
      thenHave((S(α) ∈ ω, Q(α)) |- P(α)) by Tautology

      have(∀(γ, γ ∈ ω ==> (P(γ) ==> P(S(γ))))) by Sorry //Restate.from(omegaSuccessor)
      thenHave(α ∈ ω ==> (P(α) ==> P(S(α)))) by InstantiateForall(α)
      val stepAlpha = lastStep
      have((S(α) ∈ ω, Q(α)) |- P(S(α))) by Tautology.from(
        stepAlpha,
        omegaPredecessor of (α := α)
      )
      thenHave((hyp, S(α) ∈ ω) |- P(S(α))) by Tautology
      thenHave(hyp |- S(α) ∈ ω ==> P(S(α))) by RightImplies
      thenHave(hyp ==> Q(S(α))) by Restate
      thenHave(thesis) by Generalize
    }

    val qLimit = have(∀(λ_, limitOrdinal(λ_) ==> (∀(β ∈ λ_, Q(β)) ==> Q(λ_)))) subproof {
      val h1 = limitOrdinal(λ_)
      val h2 = ∀(β ∈ λ_, Q(β))

      have((λ_ ∈ ω) |- integer(λ_)) by Sorry //Tautology.from(omegaCharacterization)
      thenHave((λ_ ∈ ω) |- ∀(β, β <= λ_ ==> (β === ∅) \/ successorOrdinal(β))) by 
        Substitute(integer.definition of (α := λ_))
      thenHave(λ_ ∈ ω |- λ_ <= λ_ ==> (λ_ === ∅) \/ successorOrdinal(λ_)) by InstantiateForall(λ_)
      val step1 = lastStep
      have(λ_ <= λ_) by Tautology
      have(λ_ ∈ ω |- (λ_ === ∅) \/ successorOrdinal(λ_)) by Tautology.from(lastStep, step1)
      val step2 = lastStep

      have(h1 |- ¬((λ_ === ∅) \/ successorOrdinal(λ_))) by Tautology.from(
        limitOrdinal.definition of (α := λ_)
      )

      have((h1, λ_ ∈ ω) |- ()) by Tautology.from(lastStep, step2)
      thenHave((h1, h2) |- λ_ ∈ ω ==> P(λ_)) by Tautology
      thenHave((h1) ==> (h2 ==> Q(λ_))) by Tautology
      thenHave(thesis) by RightForall
    }

    have(∀(α, ordinal(α) ==> Q(α))) by Tautology.from(
      transfiniteInductionCases of (P := λ(α, Q(α))),
      qZero,
      qSucc,
      qLimit
    )

    val st1 = thenHave(ordinal(α) ==> Q(α)) by InstantiateForall(α)
    have(α ∈ ω ==> ordinal(α)) by Tautology.from(omegaOrdinal)
    have(α ∈ ω ==> Q(α)) by Tautology.from(lastStep, st1)
    thenHave(α ∈ ω ==> P(α)) by Tautology
    thenHave(forall(α, α ∈ ω ==> P(α))) by RightForall
    thenHave(thesis) by Tautology
  }

}
