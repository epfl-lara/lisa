package lisa.maths.SetTheory.Types.ADT.height

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.pair
import lisa.maths.SetTheory.Types.ADT.syntax.AST.ConstructorArg

final case class HeightConstructorData(
    variables: Seq[Variable[Ind]],
    signature: Seq[(Variable[Ind], ConstructorArg)],
    subterm: Expr[Ind],
    tagTerm: Expr[Ind]
) {
  val arity: Int = signature.length
  val term = pair(tagTerm, subterm)
}
