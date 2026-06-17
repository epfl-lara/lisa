package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.FunctionAbstractions
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Pointwise uniqueness of solutions to the function's defining predicate.
 *
 * The shared part of the argument lives here: two solutions that agree
 * pointwise on the domain (and are well-typed) are equal, by functional
 * extensionality. Each strategy only has to supply the pointwise-agreement
 * sublemma [[pointwiseAgreement]]:
 *
 *   - by direct case coverage in the non-recursive case
 *     ([[lisa.maths.SetTheory.Types.ADTv2.functions.Uniqueness]]),
 *   - by well-founded induction on height in the recursive case
 *     ([[lisa.maths.SetTheory.Types.ADTv2.recursion.Uniqueness]]).
 */
trait UniquenessProof[N <: Arity] {

  protected def spec: FunSpecBase[N]

  /**
   * Pointwise agreement of any two solutions:
   *
   * `Def[f:=x] /\ Def[f:=y] |- ∀(t, t ∈ argType ==> (x * t === y * t))`.
   *
   * The bound variable may be named freely; only the shape matters.
   */
  protected def pointwiseAgreement: THM

  /**
   * `Def[f:=x] /\ Def[f:=y] ==> (x === y)` — any two solutions agree.
   */
  lazy val pointwiseUniqueness: THM =
    val xDef = spec.untypedDefinition(x)
    val yDef = spec.untypedDefinition(y)
    Lemma(xDef /\ yDef ==> (x === y)) {
      val hyp = assume(xDef /\ yDef)

      val xTyped = have(x :: (spec.argType ->: spec.returnType)) by Weakening(hyp)
      val yTyped = have(y :: (spec.argType ->: spec.returnType)) by Weakening(hyp)

      have(x === y) by Tautology.from(
        FunctionAbstractions.extensionalityStepGeneral.of(
          FunctionAbstractions.leftFunVar := x,
          FunctionAbstractions.rightFunVar := y,
          FunctionAbstractions.domainVar := spec.argType,
          FunctionAbstractions.tailTypeVar := spec.returnType
        ),
        xTyped,
        yTyped,
        pointwiseAgreement
      )
      thenHave(thesis) by Restate
    }
}
