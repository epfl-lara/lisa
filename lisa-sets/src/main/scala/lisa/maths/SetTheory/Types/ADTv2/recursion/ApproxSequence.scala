package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.Predef.app
import lisa.maths.SetTheory.Ordinals.Iteration
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingRules.functionSpaceInhabited

/**
 * Iterates the witness operator from a typed seed to construct the approximant sequence.
 */
private[recursion] final class ApproxSequence(val spec: FunSpec, val recWitness: Witness) {
  private val f0 = spec.proofVariable("f0")
  private val nVar = spec.proofVariable("nVar")
  private val valueVar = spec.proofVariable("iterationValue")
  private val F = variable[Ind >>: Ind]
  private val P = variable[Ind >>: Prop]
  private val z = variable[Ind]

  private val seedExists = Lemma(∃(f0, f0 :: spec.typ)) {
    have(thesis) by Tautology.from(recWitness.targetInhabited, functionSpaceInhabited.of(A := spec.argType, B := spec.returnType))
  }
  private val g0 = ε(f0, f0 :: spec.typ)
  private val initial = recWitness(g0)
  private val step = λ(valueVar, recWitness(valueVar))
  private val sequence = Iteration.sequence(step)(initial)

  /**
   * The approximant at the supplied natural-number index.
   */
  def G(n: Expr[Ind]): Expr[Ind] = app(sequence)(n)

  /**
   * Each successor approximant is obtained by applying the witness operator.
   */
  val approxSucc: THM = Lemma(∀(nVar ∈ N, G(S(nVar)) === recWitness(G(nVar)))) {
    have(nVar ∈ N |- G(S(nVar)) === recWitness(G(nVar))) by Restate.from(
      Iteration.successor.of(F := step, z := initial, n := nVar)
    )
    thenHave(nVar ∈ N ==> (G(S(nVar)) === recWitness(G(nVar)))) by RightImplies
    thenHave(thesis) by RightForall
  }

  /**
   * Every approximant has the function's declared type.
   */
  val approxHasType: THM = Lemma(∀(nVar ∈ N, G(nVar) :: spec.typ)) {
    val g0Typed = have(g0 :: spec.typ) by
      Cut(seedExists, Quantifiers.existsEpsilon.of(x := f0, P := λ(f0, f0 :: spec.typ)))
    val initialTyped = have(initial :: spec.typ) by Tautology.from(
      g0Typed,
      recWitness.witnessHasType.of(spec.selfPlaceholder := g0)
    )
    have((valueVar :: spec.typ) ==> (recWitness(valueVar) :: spec.typ)) by Restate.from(
      recWitness.witnessHasType.of(spec.selfPlaceholder := valueVar)
    )
    val preserved = thenHave(∀(valueVar, (valueVar :: spec.typ) ==> (recWitness(valueVar) :: spec.typ))) by RightForall
    have(thesis) by Tautology.from(
      initialTyped,
      preserved,
      Iteration.invariant.of(F := step, z := initial, P := λ(valueVar, valueVar :: spec.typ))
    )
  }
}
