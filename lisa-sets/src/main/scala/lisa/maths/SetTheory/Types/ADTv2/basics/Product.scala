package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Product {

  val product = API.defineAST(
    name = "product",
    typeVars = Seq("A","B"),
    constructors = Seq(
      ("pair", Seq(("x", "A"), ("y", "B")))
    )
  )
  val pair = product.constructors(0)
}