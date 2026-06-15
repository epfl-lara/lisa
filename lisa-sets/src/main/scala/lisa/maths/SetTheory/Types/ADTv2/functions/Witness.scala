package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.WitnessBase
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Witness construction.
 *
 * Defines the witness set
 *   W = { p ∈ A×T | caseMembership(p) }
 * and, through the shared [[CaseDefinedWitness]] core, proves `W :: A→T` and
 * the per-case equations `W(c(x̄)) = body_c`.
 *
 * Mirror of [[lisa.maths.SetTheory.Types.ADTv2.recursion.Witness]] without the
 * recursion-specific shell: there is no free self-reference and no contextual
 * typing premise, so `W` is already a solution rather than a step operator. The
 * branch return-type checks are supplied by the caller.
 */
private[functions] final class Witness[N <: Arity](
    spec: FunSpec[N]
) extends WitnessBase[N](
      functionName = spec.functionName,
      adt = spec.adt,
      argType = spec.argType,
      patternMatching = spec.patternMatching,
      returnType = spec.returnType,
      typ = spec.typ,
      typeVariablesSeq = spec.typeVariablesSeq
    ) {

  protected val checkReturnType: Map[Pattern[N], JUSTIFICATION] =
    WitnessBase.returnTypeChecks(
      patterns = spec.cases,
      returnType = spec.returnType,
      bodyAt = _.body
    )
}
