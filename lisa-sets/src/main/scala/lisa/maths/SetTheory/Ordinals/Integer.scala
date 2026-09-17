package lisa.maths.SetTheory.Ordinals

import Ordinal._
import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.EmptySet
import lisa.maths.SetTheory.Base.FoundationAxiom
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Ordinals.TransfiniteInduction.transfiniteInductionCases
import lisa.maths.SetTheory.SetTheory

/**
 * This file defines integers as ordinals whose elements are either zero
 * or successor ordinals.
 *
 * `ω` is defined as the set of all integers, and is itself an ordinal which
 * is limit.
 */
object Integer extends lisa.Main {

  private val a, b = variable[Ind]
  private val A = variable[Ind]
  private val k, n, m = variable[Ind]
  private val x = variable[Ind]
  private val α, β = variable[Ind]
  private val y, z = variable[Ind]
  private val γ, λ_ = variable[Ind]
  private val φ = variable[Ind >>: Prop]
  private val P = variable[Ind >>: Prop]

  /**
   * Definition --- An ordinal `α` is an integer if and only if all its predecessors are zero or successors.
   */
  val integer = DEF(λ(α, ∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))))

  /**
   * Definition --- The set of all integers is the set denoted `ω`.
   *
   * Its existence is guaranteed by the [[infinityAxiom]].
   */
  val ω = DEF(ε(x, ∀(α, α ∈ x <=> integer(α))))

  /**
   * Lemma --- The empty set (zero) is an integer.
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

  /**
   * Theorem --- Every integer is an ordinal.
   */
  val integerIsOrdinal = Theorem(
    integer(α) |- ordinal(α)
  ) {
    assume(integer(α))
    thenHave(∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))) by
      Substitute(integer.definition)
    thenHave((α <= α) ==> (α === ∅) \/ successorOrdinal(α)) by InstantiateForall(α)
    val splitFact = have((α === ∅) \/ successorOrdinal(α)) by Tautology.from(lastStep)

    val zeroCase = have(α === ∅ |- ordinal(α)) by Congruence.from(Ordinal.zeroOrdinal)

    val succCase = have(successorOrdinal(α) |- ordinal(α)) subproof {
      assume(successorOrdinal(α))
      val succWitness =
        thenHave(∃(γ, ordinal(γ) /\ (α === S(γ)))) by
          Substitute(successorOrdinal.definition)
      have((α === S(γ)) |- ordinal(γ) ==> ordinal(S(γ))) by Tautology.from(
        Ordinal.sucessorIsOrdinal of (α := γ)
      )
      have(α === S(γ) |- ordinal(γ) ==> ordinal(α)) by Congruence.from(lastStep)
      thenHave(ordinal(γ) /\ (α === S(γ)) |- ordinal(α)) by Tautology
      val ordFromWitness =
        thenHave(∃(γ, ordinal(γ) /\ (α === S(γ))) |- ordinal(α)) by LeftExists

      have(thesis) by Cut(succWitness, ordFromWitness)
    }

    val splitCases = have((α === ∅) \/ successorOrdinal(α) |- ordinal(α)) by LeftOr(zeroCase, succCase)
    have(thesis) by Cut(splitFact, splitCases)
  }

  /**
   * Lemma --- The successor of an integer is an integer.
   */
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

  /**
   * Lemma --- If a successor `S(α)` is an integer, then so is `α`.
   */
  private val integerPredecessor = Theorem(
    integer(S(α)) |- integer(α)
  ) {
    assume(integer(S(α)))

    val alphaInSucc = have(α ∈ S(α)) subproof {
      have(α ∈ Singleton.singleton(α)) by Tautology.from(
        Singleton.membership of (x := α, y := α)
      )
      have(α ∈ Union.∪(α)(Singleton.singleton(α))) by Tautology.from(lastStep, Union.membership of (x := α, y := Singleton.singleton(α), z := α))
      have(thesis) by Congruence.from(lastStep, S.definition)
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

  /**
   * Lemma --- Every integer belongs to any inductive set.
   */
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

    val succEq = have(SetTheory.successor(β) === S(β)) by
      Congruence.from(SetTheory.successor.definition of (x := β), S.definition of (α := β))

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
        val succAll = have(∀(γ, γ ∈ y ==> SetTheory.successor(γ) ∈ y)) by
          Tautology.from(SetTheory.inductive.definition of (x := y))
        val succAtBeta = have((β ∈ y) ==> SetTheory.successor(β) ∈ y) by InstantiateForall(β)(succAll)
        val succClosure = have((β ∈ y) ==> (S(β) ∈ y)) by
          Congruence.from(succAtBeta, succEq)
        val succInY = have(S(β) ∈ y) by Tautology.from(succClosure, betaInY)
        have(S(β) ∈ y) by Restate.from(succInY)
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

  /**
   * Lemma --- Characterization of membership in `ω`: `α ∈ ω ⇔ integer(α)`.
   */
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
      SetTheory.inductiveSetExists, {
        have(∃(i, SetTheory.inductive(i)) |- ∃(x, Q(x))) by LeftExists(existsQFromInductive)
        lastStep
      }
    )

    val qAtEpsilon = have(Q(ε(x, Q(x)))) by
      Tautology.from(existsQ, existsEpsilon of (x := x, P := λ(x, Q(x))))

    val omegaEqEpsilon = have(ω === ε(x, Q(x))) by Congruence.from(ω.definition)
    have(Q(ε(x, Q(x)))) by Restate.from(qAtEpsilon)
    val qAtOmega = thenHave(Q(ω)) by Substitute(omegaEqEpsilon)

    have(thesis) by Tautology.from(qAtOmega)
  }

  /**
   * Theorem --- Every element of `ω` is an ordinal.
   */
  val elementIsOrdinal = Theorem(α ∈ ω |- ordinal(α)) {
    have(α ∈ ω |- integer(α)) by InstantiateForall(α)(omegaCharacterization)
    have(thesis) by Tautology.from(lastStep, integerIsOrdinal)
  }

  /**
   * Comparability --- any two elements of `ω` are comparable by membership.
   */
  val comparability = Theorem((m ∈ ω, n ∈ ω) |- (m === n) \/ (m ∈ n) \/ (n ∈ m)) {
    val mOrd = have(m ∈ ω |- ordinal(m)) by Restate.from(elementIsOrdinal of (α := m))
    val nOrd = have(n ∈ ω |- ordinal(n)) by Restate.from(elementIsOrdinal of (α := n))
    have(thesis) by Tautology.from(mOrd, nOrd, Ordinal.comparability of (α := m, β := n))
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
   * Bridge theorem --- Every nonzero natural is a S of a natural.
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
   * Bridge theorem --- Induction on `ω` with S `S`.
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
    have(α ∈ ω ==> ordinal(α)) by Tautology.from(elementIsOrdinal)
    have(α ∈ ω ==> Q(α)) by Tautology.from(lastStep, st1)
    thenHave(α ∈ ω ==> P(α)) by Tautology
    thenHave(forall(α, α ∈ ω ==> P(α))) by RightForall
    thenHave(thesis) by Tautology
  }

  /**
   * Lemma --- A set is a member of its own successor: `n ∈ S(n)`.
   */
  val selfInSuccessor = Lemma(n ∈ S(n)) {
    val sn = ∪(n)(Singleton.singleton(n))
    have(n ∈ Singleton.singleton(n)) by
      Tautology.from(Singleton.membership of (x := n, y := n))
    have(n ∈ sn) by
      Tautology
        .from(lastStep, Union.membership of (x := n, y := Singleton.singleton(n), z := n))
    have(thesis) by Congruence.from(lastStep, S.definition of (α := n))
  }

  /**
   * Lemma --- The successor is injective: `n = m ⇔ S(n) = S(m)`.
   */
  val successorInjectivity = Lemma((n === m) <=> (S(n) === S(m))) {

    val forward = have(n === m |- S(n) === S(m)) by Congruence

    val hyp = S(n) === S(m)
    val eq = have(hyp |- S(n) === S(m)) by Hypothesis

    val inSuccN = have(z ∈ S(n) <=> z ∈ n \/ (z === n)) subproof {
      val succDef = have(S(n) === (n ∪ Singleton.singleton(n))) by
        Tautology.from(S.definition of (α := n))
      val unionMem = have(
        z ∈ (n ∪ Singleton.singleton(n)) <=> ((z ∈ n) \/ (z ∈ Singleton.singleton(n)))
      ) by
        Tautology.from(Union.membership of (x := n, y := Singleton.singleton(n), z := z))
      val singletonMem = have(z ∈ Singleton.singleton(n) <=> (z === n)) by
        Tautology.from(Singleton.membership of (x := n, y := z))

      val forward = have(z ∈ S(n) ==> (z ∈ n \/ (z === n))) subproof {
        assume(z ∈ S(n))
        have(z ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(succDef)
        have((z ∈ n) \/ (z ∈ Singleton.singleton(n))) by Tautology.from(lastStep, unionMem)
        have((z ∈ n) \/ (z === n)) by Tautology.from(lastStep, singletonMem)
        thenHave(thesis) by Tautology
      }

      val backward = have((z ∈ n \/ (z === n)) ==> z ∈ S(n)) subproof {
        assume(z ∈ n \/ (z === n))
        have((z ∈ n) \/ (z ∈ Singleton.singleton(n))) by Tautology.from(lastStep, singletonMem)
        have(z ∈ (n ∪ Singleton.singleton(n))) by Tautology.from(lastStep, unionMem)
        have(z ∈ S(n)) by Congruence.from(lastStep, succDef)
        thenHave(thesis) by Tautology
      }

      have(thesis) by Tautology.from(forward, backward)
    }
    val inSuccM = have(z ∈ S(m) <=> z ∈ m \/ (z === m)) by
      Restate.from(inSuccN of (n := m))
    val nInSuccMChar = have(n ∈ S(m) <=> n ∈ m \/ (n === m)) by
      Restate.from(inSuccN of (n := m, z := n))

    have(hyp /\ z ∈ n |- z ∈ S(n)) by Tautology.from(inSuccN)
    have(hyp /\ z ∈ n |- z ∈ S(m)) by Congruence.from(lastStep, eq)
    val zInMSplit = have(hyp /\ z ∈ n |- z ∈ m \/ (z === m)) by
      Tautology.from(lastStep, inSuccM)

    val zEqMCase = have((hyp /\ z ∈ n, z === m) |- z ∈ m) subproof {
      assume(hyp /\ z ∈ n)
      assume(z === m)

      val zInN = have(z ∈ n) by Tautology
      val zEqM = have(z === m) by Hypothesis
      val mInN = have(m ∈ n) by Congruence.from(zInN, zEqM)

      val nInSuccM = have(hyp |- n ∈ S(m)) by Congruence.from(selfInSuccessor of (n := n), eq)
      have(n ∈ S(m)) by Tautology.from(nInSuccM)
      val nInMSplit = have(n ∈ m \/ (n === m)) by Tautology.from(lastStep, nInSuccMChar)

      val cycleContradiction = have((m ∈ n, n ∈ m) |- ()) by Tautology.from(
        FoundationAxiom.membershipAsymmetric of (x := m, y := n)
      )
      val eqContradiction = have((m ∈ n, n === m) |- ()) subproof {
        assume(m ∈ n)
        assume(n === m)
        have(n ∈ n) by Congruence
        thenHave(thesis) by Tautology.fromLastStep(FoundationAxiom.selfNonInclusion of (x := n))
      }

      val contradiction = have((hyp /\ z ∈ n, z === m) |- ()) by
        Tautology.from(mInN, nInMSplit, cycleContradiction, eqContradiction)
      have(thesis) by Tautology.from(contradiction)
    }

    val zInMCase = have((hyp /\ z ∈ n, z ∈ m) |- z ∈ m) by Hypothesis
    val splitToInM = have((hyp /\ z ∈ n, z ∈ m \/ (z === m)) |- z ∈ m) by
      LeftOr(zInMCase, zEqMCase)

    have(hyp /\ z ∈ n |- z ∈ m) by Cut(zInMSplit, splitToInM)
    have(hyp |- z ∈ n ==> z ∈ m) by Tautology.from(lastStep)
    thenHave(hyp |- forall(z, z ∈ n ==> z ∈ m)) by RightForall
    val incl = have(hyp |- n ⊆ m) by
      Tautology.from(lastStep, subsetAxiom of (x := n, y := m))

    thenHave(hyp ==> n ⊆ m) by Restate
    thenHave(forall(n, forall(m, hyp ==> n ⊆ m))) by Generalize
    val revIncl = thenHave(hyp |- m ⊆ n) by InstantiateForall(m, n)

    val backward = have(hyp |- n === m) by
      Tautology.from(Subset.doubleInclusion of (x := n, y := m), incl, revIncl)

    have(thesis) by Tautology.from(forward, backward)
  }

  /**
   * Lemma --- A successor is never empty: `S(n) ≠ ∅`.
   */
  val zeroIsNotSucc = Lemma(!(S(n) === ∅)) {
    val sn = ∪(n)(Singleton.singleton(n))
    have(n ∈ Singleton.singleton(n)) by
      Tautology.from(Singleton.membership of (x := n, y := n))
    have(n ∈ sn) by
      Tautology
        .from(lastStep, Union.membership of (x := n, y := Singleton.singleton(n), z := n))
    have(sn =/= ∅) by
      Tautology.from(lastStep, EmptySet.setWithElementNonEmpty of (x := n, y := sn))
    have(S(n) =/= ∅) by
      Congruence.from(lastStep, S.definition of (α := n))
  }

  /**
   * Lemma --- A set is a subset of its successor: `n ⊆ S(n)`.
   */
  val subsetSuccessor = Lemma(n ⊆ S(n)) {
    val succExpanded = ∪(n)(Singleton.singleton(n))

    have(n ⊆ succExpanded) by
      Tautology.from(Union.leftSubset of (x := n, y := Singleton.singleton(n)))
    have(n ⊆ n |- n ⊆ S(n)) by
      Congruence.from(lastStep, S.definition of (α := n))
    have(thesis) by Cut(Subset.reflexivity of (x := n), lastStep)
  }

  /**
   * Lemma --- Zero is a natural number: `∅ ∈ ω`.
   */
  val emptyInOmega = Lemma(∅ ∈ ω) {
    val nullCharacterization = have((∅ ∈ ω) <=> integer(∅)) by
      InstantiateForall(∅)(omegaCharacterization)

    val leqSplit = have((b <= ∅) |- ((b ∈ ∅) \/ (b === ∅))) by Tautology
    val inEmptyCase = have((b ∈ ∅) |- (b === ∅) \/ successorOrdinal(b)) by
      Tautology.from(EmptySet.definition of (x := b))
    val eqEmptyCase = have((b === ∅) |- (b === ∅) \/ successorOrdinal(b)) by Tautology
    val fromSplit = have(((b ∈ ∅) \/ (b === ∅)) |- (b === ∅) \/ successorOrdinal(b)) by
      LeftOr(inEmptyCase, eqEmptyCase)
    have((b <= ∅) |- (b === ∅) \/ successorOrdinal(b)) by Cut(leqSplit, fromSplit)
    thenHave((b <= ∅) ==> (b === ∅) \/ successorOrdinal(b)) by RightImplies
    thenHave(forall(b, (b <= ∅) ==> (b === ∅) \/ successorOrdinal(b))) by RightForall

    have(integer(∅)) by Tautology.from(lastStep, integer.definition of (α := ∅, β := b))
    have(∅ ∈ ω) by Tautology.from(lastStep, nullCharacterization)
    have(thesis) by Restate.from(lastStep)
  }

  /**
   * Lemma --- `ω` is non-empty.
   */
  val omegaNotEmpty = Lemma(!(ω === ∅))(
    have(thesis) by Tautology.from(
      emptyInOmega,
      EmptySet.setWithElementNonEmpty of (x := ∅, y := ω)
    )
  )

  /**
   * Lemma --- `ω` is closed under successor and predecessor: `n ∈ ω ⇔ S(n) ∈ ω`.
   */
  val successorInOmega = Lemma(n ∈ ω <=> S(n) ∈ ω) {
    val toS = have(n ∈ ω |- S(n) ∈ ω) by Restate.from(omegaSuccessor of (α := n))
    val fromS = have(S(n) ∈ ω |- n ∈ ω) by
      Restate.from(omegaPredecessor of (α := n))
    have(thesis) by Tautology.from(toS, fromS)
  }

  /**
   * Lemma --- Induction over `ω`: if `P(∅)` holds and `P` is preserved by the
   * successor on `ω`, then `P` holds on all of `ω`.
   */
  val omegaSuccessorInduction = Lemma(
    (P(∅), forall(m, m ∈ ω ==> (P(m) ==> P(S(m))))) |-
      forall(n, n ∈ ω ==> P(n))
  ) {
    val stepS = have(
      forall(m, m ∈ ω ==> (P(m) ==> P(S(m)))) |-
        forall(m, m ∈ ω ==> (P(m) ==> P(S(m))))
    ) by Restate

    have(thesis) by Tautology.from(omegaInduction, stepS)
  }

  /**
   * Lemma --- `ω` is downward closed (transitive): any element of an element of
   * `ω` is itself in `ω`.
   */
  val omegaDownwardClosed = Lemma(y ∈ ω |- x ∈ y ==> x ∈ ω) {

    val Q = λ(y, x ∈ y ==> x ∈ ω)

    val zeroCase = have(Q(∅)) subproof {
      have(x ∈ ∅ |- ()) by Tautology.from(EmptySet.definition of (x := x))
      thenHave(x ∈ ∅ ==> x ∈ ω) by Tautology
      thenHave(thesis) by Restate
    }

    val recCase = have(y ∈ ω /\ Q(y) |- Q(S(y))) subproof {
      assume(y ∈ ω /\ Q(y))
      val yInN = have(y ∈ ω) by Tautology
      val ih = have(x ∈ y ==> x ∈ ω) by Tautology

      val inSuccY = have(x ∈ S(y) ==> x ∈ y \/ (x === y)) subproof {
        assume(x ∈ S(y))
        val succDef = have(S(y) === (y ∪ Singleton.singleton(y))) by
          Tautology.from(S.definition of (α := y))
        val unionMem = have(x ∈ (y ∪ Singleton.singleton(y)) <=> ((x ∈ y) \/ (x ∈ Singleton.singleton(y)))) by
          Tautology.from(Union.membership of (x := y, y := Singleton.singleton(y), z := x))
        val singletonMem = have(x ∈ Singleton.singleton(y) <=> (x === y)) by
          Tautology.from(Singleton.membership of (x := y, y := x))

        have(x ∈ (y ∪ Singleton.singleton(y))) by Congruence.from(succDef)
        have((x ∈ y) \/ (x ∈ Singleton.singleton(y))) by Tautology.from(lastStep, unionMem)
        have((x ∈ y) \/ (x === y)) by Tautology.from(lastStep, singletonMem)
        thenHave(thesis) by Tautology
      }

      val inCase = have(x ∈ y |- x ∈ ω) by Tautology.from(ih)
      val eqCase = have(x === y |- x ∈ ω) by Congruence.from(yInN)

      have(x ∈ S(y) |- x ∈ ω) by Tautology.from(inSuccY, inCase, eqCase)
      thenHave(x ∈ S(y) ==> x ∈ ω) by RightImplies
      thenHave(thesis) by Restate
    }

    have(y ∈ ω ==> (Q(y) ==> Q(S(y)))) by Tautology.from(recCase)
    thenHave(forall(y, y ∈ ω ==> (Q(y) ==> Q(S(y))))) by RightForall
    have(Q(∅) /\ forall(y, y ∈ ω ==> (Q(y) ==> Q(S(y))))) by
      Tautology.from(zeroCase, lastStep)

    have(forall(k, k ∈ ω ==> Q(k))) by
      Tautology.from(lastStep, omegaSuccessorInduction of (P := Q, m := y, n := k))
    thenHave(y ∈ ω ==> Q(y)) by InstantiateForall(y)
    thenHave(thesis) by Tautology
  }

  /**
   * Lemma --- `ω` is closed under binary union: if `a, b ∈ ω` then `a ∪ b ∈ ω`.
   */
  val unionInOmega = Lemma((a ∈ ω /\ b ∈ ω) |- (a ∪ b) ∈ ω) {

    // get ordinals from ω-membership
    have(a ∈ ω <=> integer(a)) by InstantiateForall(a)(omegaCharacterization)
    val aIsOrdinal = have(a ∈ ω |- Ordinal.ordinal(a)) by
      Tautology.from(integerIsOrdinal of (α := a), lastStep)
    have(b ∈ ω <=> integer(b)) by InstantiateForall(b)(omegaCharacterization)
    val bIsOrdinal = have(b ∈ ω |- Ordinal.ordinal(b)) by
      Tautology.from(integerIsOrdinal of (α := b), lastStep)

    // comparability: either a = b or a ∈ b or b ∈ a
    val comp = have((Ordinal.ordinal(a), Ordinal.ordinal(b)) |- (a === b) \/ (a < b) \/ (b < a)) by
      Tautology.from(Ordinal.comparability of (α := a, β := b))

    // case analysis on the disjunction
    // Case a === b
    val caseEq = have((a === b, a ∈ ω, b ∈ ω) |- (a ∪ b) ∈ ω) subproof {
      have((a === b, a ∪ b === b) |- a ∪ b === b) by Hypothesis
      have((a === b, b ∪ b === b) |- a ∪ b === b) by Congruence.from(lastStep)
      have((a === b) |- a ∪ b === b) by Congruence.from(lastStep, Union.idempotence of (x := b))
      have((a === b, b ∈ ω) |- (a ∪ b) ∈ ω) by Congruence.from(lastStep)
      have(thesis) by Tautology.from(lastStep)
    }

    // Case a < b  (i.e. a ∈ b)
    val caseALtB = have((a < b, a ∈ ω, b ∈ ω) |- (a ∪ b) ∈ ω) subproof {

      assume((a < b) /\ a ∈ ω /\ b ∈ ω)

      have(TransitiveSet.transitiveSet(b)) by
        Tautology.from(bIsOrdinal, Ordinal.ordinal.definition of (α := b))
      have(a ⊆ b) by
        Tautology.from(lastStep, TransitiveSet.elementIsSubset of (x := a, A := b))
      have((a ∪ b) ⊆ (b ∪ b)) by
        Tautology.from(lastStep, Union.leftMonotonic of (x := a, y := b, z := b))
      val unionSubset = have(a ∪ b ⊆ b) by
        Congruence.from(lastStep, Union.idempotence of (x := b))

      have(b ⊆ (a ∪ b)) by
        Tautology.from(Union.rightSubset of (x := a, y := b))
      have((a ∪ b) === b) by
        Tautology.from(unionSubset, lastStep, Subset.antisymmetry of (x := a ∪ b, y := b))
      have(thesis) by Congruence.from(lastStep)
    }

    // Symmetric case b < a
    val caseBLtA = have((b < a, a ∈ ω, b ∈ ω) |- (a ∪ b) ∈ ω) subproof {
      have(thesis) by Congruence.from(
        caseALtB of (a := b, b := a),
        Union.commutativity of (x := a, y := b)
      )
    }

    // Combine the cases coming from comparability
    have((a ∈ ω, b ∈ ω) |- (a ∪ b) ∈ ω) by
      Tautology.from(comp, caseEq, caseALtB, caseBLtA, aIsOrdinal, bIsOrdinal)
    thenHave(thesis) by Restate
  }

  /**
   * Lemma --- `ω` is inhabited: `∃n. n ∈ ω`.
   */
  val existsInOmega = Lemma(exists(n, n ∈ ω)) {
    have(thesis) by RightExists(emptyInOmega)
  }

  /**
   * Theorem --- Membership in a S: `k ∈ S(n) ⇔ k ∈ n ∨ k = n`.
   */
  val succMembership = Theorem((k ∈ S(n)) <=> (k ∈ n) \/ (k === n)) {
    val memSucc = have(k ∈ S(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
      have(k ∈ S(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
        have(k ∈ S(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by
          Congruence.from(S.definition of (α := n)),
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

  /**
   * Theorem --- Every element of `ω` is a transitive set.
   */
  val elementsTransitive = Theorem((n ∈ ω) |- TransitiveSet.transitiveSet(n)) {
    val ordN = have(n ∈ ω |- ordinal(n)) by Restate.from(elementIsOrdinal of (α := n))
    have(thesis) by Tautology.from(ordN, ordinal.definition of (α := n))
  }

  /**
   * Theorem --- A subset of `S(n)` is either all of it or a subset of `n`.
   */
  val subsetBelowSucc = Theorem((m ∈ ω, n ∈ ω, m ⊆ S(n)) |- (m === S(n)) \/ (m ⊆ n)) {
    val mInN = assume(m ∈ ω)
    val nInN = assume(n ∈ ω)
    val mSubSn = assume(m ⊆ S(n))

    val SnInN = have(S(n) ∈ ω) by
      Tautology.from(nInN, successorInOmega of (n := n))

    val cmp = have(
      (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)
    ) by Tautology.from(
      mInN,
      SnInN,
      comparability of (m := m, n := S(n))
    )

    val caseEq = have(
      m === S(n) |- (m === S(n)) \/ (m ⊆ n)
    ) by Tautology

    val caseIn = have(
      m ∈ S(n) |- (m === S(n)) \/ (m ⊆ n)
    ) subproof {
      val mInSn = assume(m ∈ S(n))
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
      S(n) ∈ m |- (m === S(n)) \/ (m ⊆ n)
    ) subproof {
      val SnInM = assume(S(n) ∈ m)
      val SnInSn = have(S(n) ∈ S(n)) by Tautology.from(
        mSubSn,
        SnInM,
        Subset.membership of (x := m, y := S(n), z := S(n))
      )
      have(thesis) by Tautology.from(
        SnInSn,
        FoundationAxiom.selfNonInclusion of (x := S(n))
      )
    }

    have(thesis) by Tautology.from(cmp, caseEq, caseIn, caseGt)
  }

}
