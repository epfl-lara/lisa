package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object List {

  val list = API.defineAST(
    name = "list",
    typeVars = Seq("A"),
    constructors =
      Seq(("nil", Seq.empty), ("cons", Seq(("head", "A"), ("tail", SelfRef))))
  )
  val nil = list.constructors(0)
  val cons = list.constructors(1)
}