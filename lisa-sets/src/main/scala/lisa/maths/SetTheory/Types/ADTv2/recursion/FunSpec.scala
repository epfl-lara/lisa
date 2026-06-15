package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.FunSpecBase
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.utils.prooflib.ProofTacticLib.Arity

class FunSpec[N <: Arity](
    override val functionName: String,
    override val adt: SemanticADT[N],
    override val argType: Expr[Ind],
    val typeSubstitutions: Seq[TypeSubstitution],
    val selfPlaceholder: Variable[Ind],
    override val patternMatching: PatternSystem[N],
    override val returnType: Expr[Ind]
) extends FunSpecBase[N](functionName, adt, argType, patternMatching, returnType) {

  protected def bodyFor(pattern: Pattern[N], fVar: Expr[Ind]): Expr[Ind] =
    pattern.body.substitute(selfPlaceholder := fVar)
}
