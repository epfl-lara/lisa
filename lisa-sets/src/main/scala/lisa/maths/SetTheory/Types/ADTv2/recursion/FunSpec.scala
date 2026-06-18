package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.FunSpecBase
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeFormula
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
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

  def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    specializeFormula(adt.height.predicate(hh), typeSubstitutions)

  val heightFun: Expr[Ind] =
    specializeTerm(adt.height.function, typeSubstitutions)

  val heightFunValid: THM = adt.height.validAt(typeSubstitutions)

  val heightZero = adt.height.zeroAt(typeSubstitutions)
}
