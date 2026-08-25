package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.functions.SemanticFunction

final class ADTFunction[S](using line: sourcecode.Line, file: sourcecode.File, sort: Sort[S])(
    semantic: SemanticFunction,
    adt: ADT[S]
) extends AbstractFunction[S](semantic, adt) {

  protected def kindLabel: String = "function"

  protected def introAppVariable: Variable[Ind] = ADTFunction.introAppVariable
}

object ADTFunction {
  private[ADTv2] val introAppVariable: Variable[Ind] =
    Variable[Ind]("functionArg")
}
