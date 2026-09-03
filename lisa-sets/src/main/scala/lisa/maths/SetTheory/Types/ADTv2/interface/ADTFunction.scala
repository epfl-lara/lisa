package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.functions.SemanticFunction
import lisa.utils.prooflib.ProofTacticLib.Arity

final class ADTFunction[N <: Arity](using line: sourcecode.Line, file: sourcecode.File, valueOfN: ValueOf[N])(
    semantic: SemanticFunction[N],
    adt: ADT[N]
) extends AbstractFunction[N](semantic, adt) {

  protected def kindLabel: String = "function"

  protected def introAppVariable: Variable[Ind] = ADTFunction.introAppVariable
}

object ADTFunction {
  private[ADTv2] val introAppVariable: Variable[Ind] =
    Variable[Ind]("functionArg")
}
