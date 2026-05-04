package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Option {

  val option = API.defineAST(
    name = "option",
    typeVars = Seq("T"),
    constructors = Seq(
      ("some", Seq(("x", "T"))),
      ("none", Seq())
    )
  )
  val some = option.constructors(0)
  val none = option.constructors(1)
}