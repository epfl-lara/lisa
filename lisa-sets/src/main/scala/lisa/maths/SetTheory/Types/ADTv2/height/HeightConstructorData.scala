package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.pair
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ConstructorArg


final case class HeightConstructorData(
    variables: Seq[Variable[Ind]],
    signature: Seq[(Variable[Ind], ConstructorArg)],
    subterm: Expr[Ind],
    tagTerm: Expr[Ind]
) {
  val arity: Int = signature.length
  val term = pair(tagTerm, subterm)
}
