package lisa.maths.SetTheory.Ordinals

import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.EmptySet
import lisa.maths.SetTheory.Base.FoundationAxiom
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Ordinals.TransfiniteInduction.transfiniteInductionCases
import lisa.maths.SetTheory.SetTheory

import Ordinal._

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
   * Membership in a successor is membership in its predecessor or equality to it.
   */
  val succMembership = Theorem((k ∈ S(n)) <=> (k ∈ n) \/ (k === n)) {
    have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
      Union.membership of (x := n, y := Singleton.singleton(n), z := k),
      Singleton.membership of (x := n, y := k)
    )
    thenHave(thesis) by Substitute(S.definition of (α := n))
  }

  /**
   * A set belongs to its own successor.
   */
  val selfInSuccessor = Lemma(n ∈ S(n)) {
    have(thesis) by Tautology.from(succMembership of (k := n))
  }

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

    val splitCases = have(β <= S(α) |- (β ∈ α) \/ (β === α) \/ (β === S(α))) by
      Tautology.from(succMembership of (k := β, n := α))

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
   * Every element of an integer is an integer.
   */
  val integerHereditary = Theorem((integer(α), β ∈ α) |- integer(β)) {
    assume(integer(α), β ∈ α)
    val memberCase = have(γ ∈ β |- γ ∈ α) by Tautology.from(
      integerIsOrdinal,
      Ordinal.transitivity of (α := γ, β := β, γ := α)
    )
    val equalityCase = have(γ === β |- γ ∈ α) by Congruence
    val belowAlpha = have(γ <= β |- γ <= α) by Tautology.from(memberCase, equalityCase)

    have(∀(γ, γ <= α ==> (γ === ∅) \/ successorOrdinal(γ))) by Tautology.from(integer.definition)
    thenHave(γ <= α ==> (γ === ∅) \/ successorOrdinal(γ)) by InstantiateForall(γ)
    have(γ <= β ==> (γ === ∅) \/ successorOrdinal(γ)) by Tautology.from(lastStep, belowAlpha)
    thenHave(∀(γ, γ <= β ==> (γ === ∅) \/ successorOrdinal(γ))) by RightForall
    thenHave(thesis) by Substitute(integer.definition of (α := β))
  }

  /**
   * If a successor is an integer, its predecessor is an integer.
   */
  private val integerPredecessor = Theorem(integer(S(α)) |- integer(α)) {
    have(thesis) by Tautology.from(
      integerHereditary of (α := S(α), β := α),
      selfInSuccessor of (n := α)
    )
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
   * Lemma --- The successor is injective: `n = m ⇔ S(n) = S(m)`.
   */
  val successorInjectivity = Lemma((n === m) <=> (S(n) === S(m))) {
    val forward = have(n === m |- S(n) === S(m)) by Congruence
    val backward = have(S(n) === S(m) |- n === m) subproof {
      assume(S(n) === S(m))
      val nInSuccessor = have(n ∈ S(m)) by Congruence.from(selfInSuccessor)
      val mInSuccessor = have(m ∈ S(n)) by Congruence.from(selfInSuccessor of (n := m))
      have(thesis) by Tautology.from(
        nInSuccessor,
        mInSuccessor,
        succMembership of (k := n, n := m),
        succMembership of (k := m),
        FoundationAxiom.membershipAsymmetric of (x := n, y := m)
      )
    }
    have(thesis) by Tautology.from(forward, backward)
  }

  /**
   * Lemma --- A successor is never empty: `S(n) ≠ ∅`.
   */
  val zeroIsNotSucc = Lemma(!(S(n) === ∅)) {
    have(thesis) by Tautology.from(selfInSuccessor, EmptySet.setWithElementNonEmpty of (x := n, y := S(n)))
  }

  /**
   * Lemma --- A set is a subset of its successor: `n ⊆ S(n)`.
   */
  val subsetSuccessor = Lemma(n ⊆ S(n)) {
    have(n ⊆ (n ∪ Singleton.singleton(n))) by Restate.from(Union.leftSubset of (x := n, y := Singleton.singleton(n)))
    thenHave(thesis) by Substitute(S.definition of (α := n))
  }

  /**
   * Lemma --- Zero is a natural number: `∅ ∈ ω`.
   */
  val emptyInOmega = Lemma(∅ ∈ ω) {
    have(∅ ∈ ω <=> integer(∅)) by InstantiateForall(∅)(omegaCharacterization)
    have(thesis) by Tautology.from(lastStep, zeroIsInteger)
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
  val omegaSuccessorInduction = omegaInduction

  /**
   * Lemma --- `ω` is downward closed (transitive): any element of an element of
   * `ω` is itself in `ω`.
   */
  val omegaDownwardClosed = Lemma(y ∈ ω |- x ∈ y ==> x ∈ ω) {
    val yCharacterization = have(y ∈ ω <=> integer(y)) by InstantiateForall(y)(omegaCharacterization)
    val xCharacterization = have(x ∈ ω <=> integer(x)) by InstantiateForall(x)(omegaCharacterization)
    have(thesis) by Tautology.from(yCharacterization, xCharacterization, integerHereditary of (α := y, β := x))
  }

  /**
   * Lemma --- `ω` is closed under binary union: if `a, b ∈ ω` then `a ∪ b ∈ ω`.
   */
  val unionInOmega = Lemma((a ∈ ω /\ b ∈ ω) |- (a ∪ b) ∈ ω) {
    assume(a ∈ ω, b ∈ ω)
    val equalCase = have(a === b |- (a ∪ b) ∈ ω) by
      Congruence.from(Union.idempotence of (x := b))

    val leftCase = have(a ∈ b |- (a ∪ b) ∈ ω) subproof {
      assume(a ∈ b)
      have(TransitiveSet.transitiveSet(b)) by
        Tautology.from(elementIsOrdinal of (α := b), ordinal.definition of (α := b))
      val included = have(a ⊆ b) by
        Tautology.from(lastStep, TransitiveSet.elementIsSubset of (x := a, A := b))
      have((a ∪ b) ⊆ b) by Tautology.from(
        included,
        Subset.reflexivity of (x := b),
        Union.leftUnionSubset of (x := a, y := b, z := b)
      )
      have((a ∪ b) === b) by Tautology.from(
        lastStep,
        Union.rightSubset of (x := a, y := b),
        Subset.antisymmetry of (x := a ∪ b, y := b)
      )
      have(thesis) by Congruence.from(lastStep)
    }
    val rightCase = have(b ∈ a |- (a ∪ b) ∈ ω) by
      Congruence.from(leftCase of (a := b, b := a), Union.commutativity of (x := a, y := b))

    have(thesis) by Tautology.from(comparability of (m := a, n := b), equalCase, leftCase, rightCase)
  }

  /**
   * Lemma --- `ω` is inhabited: `∃n. n ∈ ω`.
   */
  val existsInOmega = Lemma(exists(n, n ∈ ω)) {
    have(thesis) by RightExists(emptyInOmega)
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
