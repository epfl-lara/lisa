package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Bool {

  val bool = API.defineAST(
    name = "bool",
    typeVars = Seq.empty,
    constructors = Seq(
      ("tru", Seq.empty),
      ("fals", Seq.empty)
    )
  )
  val tru = bool.constructors(0)
  val fals = bool.constructors(1)
}