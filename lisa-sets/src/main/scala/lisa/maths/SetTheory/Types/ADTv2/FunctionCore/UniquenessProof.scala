package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
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

      have(thesis) by Tautology.from(
        BasicTheorems.functionalExtentionality of (
          f := x,
          g := y,
          A := spec.argType,
          B := spec.returnType
        ),
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := x,
          A := spec.argType,
          B := spec.returnType
        ),
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := y,
          A := spec.argType,
          B := spec.returnType
        ),
        pointwiseAgreement
      )
    }
}
