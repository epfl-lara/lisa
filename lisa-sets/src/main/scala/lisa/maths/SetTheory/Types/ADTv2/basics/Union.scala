package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Union {

  val union = API.defineAST(
    name = "union",
    typeVars = Seq("A","B"),
    constructors = Seq(
      ("inl", Seq(("x", "A"))),
      ("inr", Seq(("y", "B")))
    )
  )
  val inl = union.constructors(0)
  val inr = union.constructors(1)
}