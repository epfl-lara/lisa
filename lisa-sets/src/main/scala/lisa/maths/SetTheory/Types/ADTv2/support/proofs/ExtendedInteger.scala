package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.EmptySet
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Ordinals.Ordinal
import lisa.maths.SetTheory.Ordinals.Ordinal.<=
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.Ordinals.Ordinal.limitOrdinal
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinal
import lisa.maths.SetTheory.Ordinals.Ordinal.successorOrdinal
import lisa.maths.SetTheory.Ordinals.TransfiniteInduction.transfiniteInductionCases
import lisa.maths.SetTheory.SetTheory

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
  private val γ, λ_ = variable[Ind]
  private val φ = variable[Ind >>: Prop]
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
      val succWitness =
        thenHave(∃(γ, ordinal(γ) /\ (α === S(γ)))) by
          Substitute(successorOrdinal.definition)
      have( (α === S(γ)) |- ordinal(γ) ==> ordinal(S(γ))) by Tautology.from(
        Ordinal.sucessorIsOrdinal of (α := γ)
      )
      have( α === S(γ) |- ordinal(γ) ==>  ordinal(α)) by Congruence.from(lastStep)
      thenHave(ordinal(γ) /\ (α === S(γ)) |- ordinal(α)) by Tautology
      val ordFromWitness =
        thenHave(∃(γ, ordinal(γ) /\ (α === S(γ))) |- ordinal(α)) by LeftExists

      have(thesis) by Cut(succWitness, ordFromWitness)
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
      val inSuccSplit = thenHave(β ∈ Union.∪(α)(Singleton.singleton(α)) \/ (β === S(α))) by Substitute(S.definition)
      val inUnionToLeft = have(β ∈ Union.∪(α)(Singleton.singleton(α)) ==> (β ∈ α) \/ (β === α)) by Tautology.from(
        Union.membership of (x := α, y := Singleton.singleton(α), z := β),
        Singleton.membership of (x := α, y := β)
      )
      have(thesis) by Tautology.from(inSuccSplit, inUnionToLeft)
    }

    val splitCases = lastStep

    val intAll = have(∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))) by
      Tautology.from(integer.definition)
    val intAtBeta = have(β <= α ==> (β === ∅) \/ successorOrdinal(β)) by InstantiateForall(β)(intAll)

    val inAlphaCase = have(β ∈ α |- (β === ∅) \/ successorOrdinal(β)) by
      Tautology.from(intAtBeta)

    val intAtAlpha = have(α <= α ==> (α === ∅) \/ successorOrdinal(α)) by InstantiateForall(α)(intAll)
    have((α === ∅) \/ successorOrdinal(α)) by Tautology.from(intAtAlpha)
    val eqAlphaCase = have((β === α) |- (β === ∅) \/ successorOrdinal(β)) by
      Congruence.from(lastStep)

    val eqSuccCase = have((β === S(α)) |- (β === ∅) \/ successorOrdinal(β)) subproof {
      assume(β === S(α))
      val ordAlpha = have(ordinal(α)) by Tautology.from(integerIsOrdinal)
      have(S(α) === S(α)) by Restate
      have(ordinal(α) /\ (S(α) === S(α))) by Tautology.from(ordAlpha, lastStep)
      thenHave(∃(γ, ordinal(γ) /\ (S(α) === S(γ)))) by RightExists
      have(successorOrdinal(S(α))) by Tautology.from(
        lastStep,
        successorOrdinal.definition of (α := S(α))
      )
      thenHave((β === S(α)) |- successorOrdinal(β)) by Congruence
      have(thesis) by Tautology.from(lastStep)
    }

    val splitToGoal = have(
      (β ∈ α) \/ (β === α) \/ (β === S(α)) |- (β === ∅) \/ successorOrdinal(β)
    ) by Tautology.from(inAlphaCase, eqAlphaCase, eqSuccCase)

    have(β <= S(α) |- (β === ∅) \/ successorOrdinal(β)) by Cut(splitCases, splitToGoal)
    thenHave((β <= S(α)) ==> (β === ∅) \/ successorOrdinal(β)) by RightImplies
    thenHave(∀(β, (β <= S(α)) ==> (β === ∅) \/ successorOrdinal(β))) by RightForall
    thenHave(thesis) by Substitute(integer.definition of (α := S(α)))
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


    val inAlphaToLeqSucc = have(β ∈ α |- β <= S(α)) subproof {
      assume(β ∈ α)
      have(β ∈ Union.∪(α)(Singleton.singleton(α))) by Tautology.from(
        lastStep,
        Union.membership of (x := α, y := Singleton.singleton(α), z := β)
      )
      have(β ∈ S(α)) by Congruence.from(lastStep, S.definition)
      have(thesis) by Tautology.from(lastStep)
    }

    val eqAlphaToLeqSucc = have((β === α) |- β <= S(α)) subproof {
      assume(β === α)
      have(β ∈ S(α)) by Congruence.from(alphaInSucc)
      have(thesis) by Tautology.from(lastStep)
    }
    val betaLeqSucc = have(β <= α |- β <= S(α)) by Tautology.from(inAlphaToLeqSucc, eqAlphaToLeqSucc)

    have(∀(β, β <= S(α) ==> (β === ∅) \/ successorOrdinal(β))) by
      Tautology.from(integer.definition of (α := S(α)))
    thenHave(β <= S(α) ==> (β === ∅) \/ successorOrdinal(β)) by InstantiateForall(β)
    val predAtBeta = lastStep

    have(β <= α |- (β === ∅) \/ successorOrdinal(β)) by Tautology.from(betaLeqSucc, predAtBeta)
    thenHave((β <= α) ==> (β === ∅) \/ successorOrdinal(β)) by RightImplies
    thenHave(∀(β, (β <= α) ==> (β === ∅) \/ successorOrdinal(β))) by RightForall
    thenHave(thesis) by Substitute(integer.definition)
  }

  private val integerInInductive = Lemma(
    (SetTheory.inductive(y), integer(α)) |- α ∈ y
  ) {
    def PInt(t: Expr[Ind]): Expr[Prop] = integer(t) ==> t ∈ y

    val zeroCase = have(SetTheory.inductive(y) |- PInt(∅)) subproof {
      assume(SetTheory.inductive(y))
      have(∅ ∈ y) by Tautology.from(SetTheory.inductive.definition of (x := y))
      have(integer(∅) ==> (∅ ∈ y)) by Tautology.from(lastStep)
      have(thesis) by Tautology.from(lastStep)
    }

    val succEq = have(S(β) === SetTheory.successor(β)) by
      Congruence.from(S.definition of (α := β), SetTheory.successor.definition of (x := β))

    val succCase = have(
      SetTheory.inductive(y) |- ∀(β, ordinal(β) /\ PInt(β) ==> PInt(S(β)))
    ) subproof {
      assume(SetTheory.inductive(y))
      have(ordinal(β) /\ PInt(β) |- PInt(S(β))) subproof {
        assume(ordinal(β) /\ PInt(β))
        val ih = have(PInt(β)) by Tautology
        assume(integer(S(β)))
        val predInt = have(integer(β)) by Tautology.from(integerPredecessor of (α := β))
        val betaInY = have(β ∈ y) by Tautology.from(ih, predInt)
        have(∀(γ, γ ∈ y ==> SetTheory.successor(γ) ∈ y)) by
          Tautology.from(SetTheory.inductive.definition of (x := y))
        val succClosure = thenHave((β ∈ y) ==> (SetTheory.successor(β) ∈ y)) by
          InstantiateForall(β)
        val succInY = have(SetTheory.successor(β) ∈ y) by Tautology.from(succClosure, betaInY)
        have(S(β) ∈ y) by Congruence.from(succInY, succEq)
        have((SetTheory.inductive(y), ordinal(β) /\ PInt(β)) |- integer(S(β)) ==> (S(β) ∈ y)) by
          Tautology.from(lastStep)
        have(thesis) by Tautology.from(lastStep)
      }
      thenHave(ordinal(β) /\ PInt(β) ==> PInt(S(β))) by Restate
      thenHave(thesis) by RightForall
    }

    val limitCase = have(
      SetTheory.inductive(y) |- ∀(λ_, limitOrdinal(λ_) ==> (∀(β ∈ λ_, PInt(β)) ==> PInt(λ_)))
    ) subproof {
      assume(SetTheory.inductive(y))
      have(limitOrdinal(λ_) ==> (∀(β ∈ λ_, PInt(β)) ==> PInt(λ_))) subproof {
        assume(limitOrdinal(λ_))
        assume(∀(β ∈ λ_, PInt(β)))
        assume(integer(λ_))

        have(integer(λ_) |- integer(λ_)) by Restate
        thenHave(integer(λ_) |- ∀(β, β <= λ_ ==> (β === ∅) \/ successorOrdinal(β))) by
          Substitute(integer.definition of (α := λ_))
        val intAtSelf = thenHave(integer(λ_) |- λ_ <= λ_ ==> (λ_ === ∅) \/ successorOrdinal(λ_)) by
          InstantiateForall(λ_)

        val selfLeq = have((λ_ ∈ λ_) \/ (λ_ === λ_)) by Tautology
        val intSplit = have(
          (limitOrdinal(λ_), ∀(β ∈ λ_, PInt(β)), integer(λ_), SetTheory.inductive(y)) |-
            (λ_ === ∅) \/ successorOrdinal(λ_)
        ) by
          Tautology.from(intAtSelf, selfLeq)

        val notSplit = have(limitOrdinal(λ_) |- ¬((λ_ === ∅) \/ successorOrdinal(λ_))) by
          Tautology.from(limitOrdinal.definition of (α := λ_))

        have((limitOrdinal(λ_), ∀(β ∈ λ_, PInt(β)), integer(λ_), SetTheory.inductive(y)) |- ()) by
          Tautology.from(intSplit, notSplit)
        have((limitOrdinal(λ_), ∀(β ∈ λ_, PInt(β)), integer(λ_)) |- λ_ ∈ y) by Tautology.from(lastStep)
        have((limitOrdinal(λ_), ∀(β ∈ λ_, PInt(β))) |- integer(λ_) ==> (λ_ ∈ y)) by
          Tautology.from(lastStep)
        have(thesis) by Tautology.from(lastStep)
      }
      thenHave(thesis) by RightForall
    }

    val ordCases = have(SetTheory.inductive(y) |- ∀(β, ordinal(β) ==> PInt(β))) by
      Tautology.from(
        zeroCase,
        succCase,
        limitCase,
        transfiniteInductionCases of (P := λ(β, PInt(β)))
      )

    val atAlpha = have(SetTheory.inductive(y) |- ordinal(α) ==> PInt(α)) by
      InstantiateForall(α)(ordCases)

    val alphaOrd = have((SetTheory.inductive(y), integer(α)) |- ordinal(α)) by
      Tautology.from(integerIsOrdinal)

    val alphaP = have((SetTheory.inductive(y), integer(α)) |- PInt(α)) by
      Tautology.from(alphaOrd, atAlpha)

    have(thesis) by Tautology.from(alphaP)
  }

  val omegaCharacterization = Lemma(∀(α, α ∈ ω <=> integer(α))) {
    def Q(s: Expr[Ind]): Expr[Prop] = ∀(α, α ∈ s <=> integer(α))
    def R(i: Expr[Ind], s: Expr[Ind]): Expr[Prop] = ∀(β, β ∈ s <=> (β ∈ i) /\ integer(β))

    val i = variable[Ind]
    val s = variable[Ind]

    val existsQFromInductive = have(SetTheory.inductive(i) |- ∃(x, Q(x))) subproof {
      assume(SetTheory.inductive(i))

      val existsR = have(∃(s, R(i, s))) by
        Weakening(lisa.maths.SetTheory.Base.Comprehension.existence of (y := i, φ := λ(β, integer(β))))

      val epsSet: Expr[Ind] = ε(s, R(i, s))
      val rAtEps = have(R(i, epsSet)) by
        Tautology.from(existsR, existsEpsilon of (x := s, P := λ(s, R(i, s))))

      val rAtBeta = have(β ∈ epsSet <=> (β ∈ i) /\ integer(β)) by
        InstantiateForall(β)(rAtEps)

      val forward = have(β ∈ epsSet ==> integer(β)) by Tautology.from(
        rAtBeta
      )

      val inInductive = have(integer(β) ==> β ∈ i) by
        Tautology.from(integerInInductive of (y := i, α := β))

      val backward = have(integer(β) ==> β ∈ epsSet) by Tautology.from(
        rAtBeta,
        inInductive
      )

      have(β ∈ epsSet <=> integer(β)) by Tautology.from(forward, backward)
      thenHave(∀(β, β ∈ epsSet <=> integer(β))) by RightForall
      thenHave(∃(x, Q(x))) by RightExists
      have(thesis) by Tautology.from(lastStep)
    }

    val existsQ = have(∃(x, Q(x))) by Cut(
      SetTheory.inductiveSetExists,
      {
        have(∃(i, SetTheory.inductive(i)) |- ∃(x, Q(x))) by LeftExists(existsQFromInductive)
        lastStep
      }
    )

    val qAtEpsilon = have(Q(ε(x, Q(x)))) by
      Tautology.from(existsQ, existsEpsilon of (x := x, P := λ(x, Q(x))))

    val omegaEqEpsilon = have(ω === ε(x, Q(x))) by Congruence.from(Integer.ω.definition)
    have(Q(ε(x, Q(x)))) by Restate.from(qAtEpsilon)
    val qAtOmega = thenHave(Q(ω)) by Substitute(omegaEqEpsilon)

    have(thesis) by Tautology.from(qAtOmega)
  }

  val omegaOrdinal = Theorem(α ∈ ω |- ordinal(α)) {
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
   * Bridge theorem --- Every nonzero natural is a successor of a natural.
   */
  val nonZeroOmegaHasPredecessor = Theorem(
    (α ∈ ω, α =/= ∅) |- ∃(β, β ∈ ω /\ (α === S(β)))
  ) {
    assume(α ∈ ω)
    assume(α =/= ∅)

    val alphaIsInteger = have(integer(α)) by InstantiateForall(α)(omegaCharacterization)
    val intPreds = have(∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))) by
      Substitute(integer.definition.of(α := α))(alphaIsInteger)
    val succSplit = have((α === ∅) \/ successorOrdinal(α)) by Tautology.from(
      have(α <= α ==> (α === ∅) \/ successorOrdinal(α)) by InstantiateForall(α)(intPreds)
    )
    val succOrdinalAtAlpha = have(successorOrdinal(α)) by Tautology.from(succSplit, have(!(α === ∅)) by Tautology)

    val succWitness = have(∃(γ, ordinal(γ) /\ (α === S(γ)))) by Tautology.from(
      succOrdinalAtAlpha,
      have(successorOrdinal(α) ==> ∃(γ, ordinal(γ) /\ (α === S(γ)))) by
        Tautology.from(successorOrdinal.definition.of(α := α))
    )

    val omegaWitnessBranch = have((ordinal(γ) /\ (α === S(γ))) |- ∃(β, β ∈ ω /\ (α === S(β)))) subproof {
      assume(ordinal(γ) /\ (α === S(γ)))
      val alphaEqSucc = have(α === S(γ)) by Tautology
      val succInOmega = have(S(γ) ∈ ω) by Congruence.from(have(α ∈ ω) by Tautology, alphaEqSucc)
      val gammaInOmega = have(γ ∈ ω) by Tautology.from(
        succInOmega,
        omegaPredecessor.of(α := γ)
      )
      have(γ ∈ ω /\ (α === S(γ))) by Tautology.from(gammaInOmega, alphaEqSucc)
      thenHave(∃(β, β ∈ ω /\ (α === S(β)))) by RightExists
    }
    val omegaWitness = have(∃(γ, ordinal(γ) /\ (α === S(γ))) |- ∃(β, β ∈ ω /\ (α === S(β)))) by
      LeftExists.withParameters(ordinal(γ) /\ (α === S(γ)), γ)(omegaWitnessBranch)

    have(thesis) by Cut(succWitness, omegaWitness)
  }

  /**
   * Bridge theorem --- Induction on `ω` with successor `S`.
   */
  val omegaInduction = Theorem(
    (P(∅), ∀(α, α ∈ ω ==> (P(α) ==> P(S(α))))) |- ∀(α, α ∈ ω ==> P(α))
  ) {
    def Q(t: Expr[Ind]): Expr[Prop] = t ∈ ω ==> P(t)
    val succStepAssumption = ∀(γ, γ ∈ ω ==> (P(γ) ==> P(S(γ))))

    assume(P(∅))
    assume(succStepAssumption)

    val qZero = have(P(∅) |- Q(∅)) subproof {
      val zeroChar = have(∅ ∈ ω <=> integer(∅)) by InstantiateForall(∅)(omegaCharacterization)
      val zeroInOmega = have(∅ ∈ ω) by Tautology.from(
        zeroIsInteger,
        zeroChar
      )
      have(thesis) by Tautology.from(zeroInOmega)
    }

    val qSucc = have(succStepAssumption |- ∀(α, ordinal(α) /\ Q(α) ==> Q(S(α)))) subproof {
      val hyp = ordinal(α) /\ Q(α)
      // assume(ordinal(α) /\ Q(α))
      have(hyp |- Q(α)) by Tautology

      have(S(α) ∈ ω |- α ∈ ω) by Tautology.from(omegaPredecessor)
      thenHave((S(α) ∈ ω, Q(α)) |- P(α)) by Tautology

      have(succStepAssumption |- succStepAssumption) by Hypothesis
      thenHave(succStepAssumption |- α ∈ ω ==> (P(α) ==> P(S(α)))) by InstantiateForall(α)
      val stepAlpha = lastStep
      have((succStepAssumption, S(α) ∈ ω, Q(α)) |- P(S(α))) by Tautology.from(
        stepAlpha,
        omegaPredecessor of (α := α)
      )
      thenHave((succStepAssumption, hyp, S(α) ∈ ω) |- P(S(α))) by Tautology
      have((succStepAssumption, hyp) |- S(α) ∈ ω ==> P(S(α))) by Tautology.from(lastStep)
      thenHave((succStepAssumption, hyp) |- Q(S(α))) by Restate
      have(succStepAssumption |- hyp ==> Q(S(α))) by Tautology.from(lastStep)
      thenHave(thesis) by Generalize
    }

    val qZeroFact = have(Q(∅)) by Tautology.from(qZero)
    val qSuccFact = have(∀(α, ordinal(α) /\ Q(α) ==> Q(S(α)))) by Tautology.from(qSucc)

    val qLimit = have(∀(λ_, limitOrdinal(λ_) ==> (∀(β ∈ λ_, Q(β)) ==> Q(λ_)))) subproof {
      val h1 = limitOrdinal(λ_)
      val h2 = ∀(β ∈ λ_, Q(β))

      val lambdaChar = have(λ_ ∈ ω <=> integer(λ_)) by InstantiateForall(λ_)(omegaCharacterization)
      have((λ_ ∈ ω) |- integer(λ_)) by Tautology.from(
        lambdaChar
      )
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
      qZeroFact,
      qSuccFact,
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
