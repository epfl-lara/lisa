package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.recursion.SemanticFunction

final class RecFunction[S](using line: sourcecode.Line, file: sourcecode.File, sort: Sort[S])(
    semantic: SemanticFunction,
    adt: ADT[S]
) extends AbstractFunction[S](semantic, adt) {

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
