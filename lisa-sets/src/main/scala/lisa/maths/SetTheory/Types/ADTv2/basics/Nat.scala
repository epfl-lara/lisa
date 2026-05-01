package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Nat {

  val nat = API.defineAST(
    name = "nat",
    typeVars = Seq.empty,
    constructors = Seq(
      ("zero", Seq.empty),
      ("succ", Seq(("k", SelfRef)))
    )
  )
  val zero = nat.constructors(0)
  val succ = nat.constructors(1)
}