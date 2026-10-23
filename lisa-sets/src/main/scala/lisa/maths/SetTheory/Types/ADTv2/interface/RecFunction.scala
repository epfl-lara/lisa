package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.recursion.SemanticFunction
import lisa.utils.prooflib.ProofTacticLib.Arity

final class RecFunction[N <: Arity](using line: sourcecode.Line, file: sourcecode.File, valueOfN: ValueOf[N])(
    semantic: SemanticFunction[N],
    adt: ADT[N]
) extends AbstractFunction[N](semantic, adt) {

  protected def kindLabel: String = "recursive function"

  protected def introAppVariable: Variable[Ind] = RecFunction.introAppVariable
}

object RecFunction {
  def selfReferenceName(functionName: String): String = s"${functionName}RecSelf"

  def selfPlaceholder(functionName: String): Variable[Ind] =
    Variable[Ind](selfReferenceName(functionName))

  private[ADTv2] val introAppVariable: Variable[Ind] =
    Variable[Ind]("recFunctionArg")
}
