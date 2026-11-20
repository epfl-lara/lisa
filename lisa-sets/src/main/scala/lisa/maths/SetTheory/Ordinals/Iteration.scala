package lisa.maths.SetTheory.Ordinals

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.emptyInOmega
import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Integer.selfInSuccessor
import lisa.maths.SetTheory.Ordinals.Integer.successorInOmega
import lisa.maths.SetTheory.Ordinals.Integer.ω
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.Thm

/**
 * Iteration of a class functional on the natural numbers, with invariant preservation.
 */
object Iteration {
  private val F = variable[Ind >>: Ind]
  private val P = variable[Ind >>: Prop]
  private val z, n, j, h, y, x, g, m, f, A = variable[Ind]
  private val Func = variable[Ind >>: Ind >>: Ind]
  private val α = variable[Ind]

  private val step = λ(n, λ(h, ε(y, ((n === ∅) /\ (y === z)) \/ ∃(j, (j ∈ ω) /\ (n === S(j)) /\ (y === F(app(h)(j)))))))
  private val recursion = TransfiniteRecursion.transfiniteRecursionFunction(step)(ω)

  /**
   * The sequence starting at `z` and applying `F` at each successor.
   */
  val sequence = DEF(λ(F, λ(z, recursion)))

  private val seq = sequence(F)(z)
  private def value(index: Expr[Ind]): Expr[Ind] = app(seq)(index)
  private def specification(graph: Expr[Ind]): Expr[Prop] =
    functionOn(graph)(ω) /\ ∀(n ∈ ω, app(graph)(n) === step(n)(graph ↾ n))

  private val recursionSpec = Theorem(specification(seq)) {
    val raw = have(specification(recursion)) by Cut(
      OmegaFacts.isOrdinal,
      TransfiniteRecursion.transfiniteRecursionFunctionSpec.of(Func := step, α := ω)
    )
    val equality = have(recursion === seq) by Congruence.from(sequence.definition)
    val transported = have(recursion === seq |- specification(seq)) by
      RightSubst(Seq(recursion -> seq), Seq(g) -> specification(g))(raw)
    have(thesis) by Cut(equality, transported)
  }

  /**
   * The iteration sequence is a function whose domain is omega.
   */
  val functionOnOmega = Theorem(functionOn(seq)(ω)) {
    have(thesis) by Weakening(recursionSpec)
  }

  private def valueAt(using
      proof: lisa.SetTheoryLibrary.ProofBuilder
  )(
      index: Expr[Ind],
      indexInOmega: Thm,
      predicate: Expr[Ind >>: Prop],
      target: Expr[Ind],
      existence: Thm,
      uniqueness: Thm
  ): Thm = {
    val equations = have(∀(n ∈ ω, value(n) === step(n)(seq ↾ n))) by Weakening(recursionSpec)
    val atIndex = have(index ∈ ω |- value(index) === step(index)(seq ↾ index)) by InstantiateForall(index)(equations)
    val chosen = ε(y, predicate(y))
    val chosenProperty = have(predicate(chosen)) by
      Cut(existence, Quantifiers.existsEpsilon.of(x := y, P := predicate))
    val chosenEquality = have(chosen === target) by Tautology.from(
      chosenProperty,
      have(predicate(chosen) ==> (chosen === target)) by InstantiateForall(chosen)(uniqueness)
    )
    val stepEquality = have(step(index)(seq ↾ index) === chosen) by Restate
    have(value(index) === target) by Congruence.from(atIndex, indexInOmega, stepEquality, chosenEquality)
  }

  /**
   * Iteration starts at its supplied initial value.
   */
  val zero = Theorem(value(∅) === z) {
    val successorBody = (j ∈ ω) /\ (∅ === S(j)) /\ (y === F(app(seq ↾ ∅)(j)))
    val predicate = λ(y, ((∅ === ∅) /\ (y === z)) \/ ∃(j, successorBody))
    have(predicate(z)) by Restate
    val existence = thenHave(∃(y, predicate(y))) by RightExists

    val zeroIsSuccessor = have(successorBody |- ∅ === S(j)) by Restate
    val impossibleEquality = have(successorBody |- S(j) === ∅) by Congruence.from(zeroIsSuccessor)
    have(successorBody |- ()) by Tautology.from(impossibleEquality, Integer.zeroIsNotSucc.of(n := j))
    val noSuccessor = thenHave(∃(j, successorBody) |- ()) by LeftExists
    have(predicate(y) ==> (y === z)) by Tautology.from(noSuccessor)
    val uniqueness = thenHave(∀(y, predicate(y) ==> (y === z))) by RightForall
    have(thesis) by Restate.from(valueAt(∅, emptyInOmega, predicate, z, existence, uniqueness))
  }

  /**
   * At a successor, iteration applies its step functional to the preceding value.
   */
  val successor = Theorem(n ∈ ω |- value(S(n)) === F(value(n))) {
    val nInOmega = assume(n ∈ ω)
    val successorInNat = have(S(n) ∈ ω) by Tautology.from(nInOmega, successorInOmega)
    val history = seq ↾ S(n)
    val target = F(app(history)(n))
    val successorBody = (j ∈ ω) /\ (S(n) === S(j)) /\ (y === F(app(history)(j)))
    val predicate = λ(y, ((S(n) === ∅) /\ (y === z)) \/ ∃(j, successorBody))

    have((n ∈ ω) /\ (S(n) === S(n)) /\ (target === F(app(history)(n)))) by Restate.from(nInOmega)
    thenHave(∃(j, (j ∈ ω) /\ (S(n) === S(j)) /\ (target === F(app(history)(j))))) by RightExists
    thenHave(predicate(target)) by Weakening
    val existence = thenHave(∃(y, predicate(y))) by RightExists

    val predecessorEquality = have(successorBody |- n === j) by Weakening(Integer.successorInjectivity.of(m := j))
    val successorValue = have(successorBody |- y === F(app(history)(j))) by Restate
    have(successorBody |- y === target) by Congruence.from(predecessorEquality, successorValue)
    val fromSuccessor = thenHave(∃(j, successorBody) |- y === target) by LeftExists
    have(predicate(y) ==> (y === target)) by Tautology.from(fromSuccessor, Integer.zeroIsNotSucc)
    val uniqueness = thenHave(∀(y, predicate(y) ==> (y === target))) by RightForall

    val domain = have(dom(seq) === ω) by Tautology.from(
      functionOnOmega,
      BasicTheorems.functionOnDomain.of(f := seq, A := ω)
    )
    val inDomain = have(n ∈ dom(seq)) by Congruence.from(domain, nInOmega)
    val restrictedValue = have(app(history)(n) === value(n)) by Tautology.from(
      Restriction.restrictedApp.of(f := seq, x := n, A := S(n)),
      BasicTheorems.functionOnIsFunction.of(f := seq, A := ω),
      functionOnOmega,
      inDomain,
      selfInSuccessor
    )
    have(thesis) by Congruence.from(
      valueAt(S(n), successorInNat, predicate, target, existence, uniqueness),
      restrictedValue
    )
  }

  /**
   * A predicate containing the seed and preserved by the step holds at every index.
   */
  val invariant = Theorem(
    (P(z), ∀(x, P(x) ==> P(F(x)))) |- ∀(n ∈ ω, P(value(n)))
  ) {
    val seed = assume(P(z))
    val preserved = assume(∀(x, P(x) ==> P(F(x))))
    val property = λ(n, P(value(n)))
    val base = have(P(value(∅))) by Congruence.from(seed, zero)
    have(n ∈ ω ==> (P(value(n)) ==> P(value(S(n))))) subproof {
      assume(n ∈ ω)
      val inductionHypothesis = assume(P(value(n)))
      val stepAtValue = have(P(value(n)) ==> P(F(value(n)))) by InstantiateForall(value(n))(preserved)
      val next = have(P(F(value(n)))) by Tautology.from(inductionHypothesis, stepAtValue)
      have(P(value(S(n)))) by Congruence.from(next, successor)
      thenHave(thesis) by Restate
    }
    val inductionStep = thenHave(∀(n, n ∈ ω ==> (P(value(n)) ==> P(value(S(n)))))) by RightForall
    have(thesis) by Tautology.from(omegaSuccessorInduction.of(P := property), base, inductionStep)
  }
}
