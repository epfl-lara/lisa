package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.FunSpecBase
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Specification of a (non-recursive) function defined by pattern matching.
 *
 * Mirror of [[lisa.maths.SetTheory.Types.ADTv2.recursion.FunSpec]] with the
 * recursion-specific machinery (`selfPlaceholder`, `typeSubstitutions`) erased:
 * since the bodies do not mention the function being defined, the defining
 * predicate refers directly to the candidate witness `fVar`.
 *
 * Holds the shared parameters consumed by [[Witness]] and [[Existence]].
 */
private[functions] final class FunSpec[N <: Arity](
    override val functionName: String,
    override val adt: SemanticADT[N],
    override val argType: Expr[Ind],
    override val patternMatching: PatternSystem[N],
    override val returnType: Expr[Ind]
) extends FunSpecBase[N](functionName, adt, argType, patternMatching, returnType) {

  // No self-reference here, so the placeholder is just a fresh candidate. It must
  // be fresh w.r.t. every variable occurring in the patterns: a pattern *binder*
  // sharing the candidate's name (even though the bodies never reference the
  // function) would be captured when `definitionAt` substitutes the placeholder.
  override val placeholder: Variable[Ind] =
    Variable[Ind](freshId(cases.flatMap(p => p.binders :+ p.inputTerm :+ p.body), functionName))

  protected def bodyFor(pattern: Pattern[N], fVar: Expr[Ind]): Expr[Ind] =
    pattern.body
}
