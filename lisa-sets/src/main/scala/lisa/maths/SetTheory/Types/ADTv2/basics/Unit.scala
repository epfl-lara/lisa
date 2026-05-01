package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Unit {

  val unit = API.defineAST(
    name = "unit",
    typeVars = Seq.empty,
    constructors = Seq(
      ("star", Seq.empty)
    )
  )
  val star = unit.constructors(0)
}