package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Box {

  val box = API.defineAST(
    name = "box",
    typeVars = Seq("A"),
    constructors = Seq(
      ("pack", Seq(("x", "A")))
    )
  )
  val pack = box.constructors(0)
}