package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef
import lisa.maths.SetTheory.Types.TypingHelpers

private val natPredN = variable[Ind]
private val natDoubleN = variable[Ind]
private val natAddN = variable[Ind]
private val natAddRight = variable[Ind]

val nat = adt(
  name = "nat",
  constructors = Seq(
    ("zero", Seq.empty),
    ("succ", Seq(("k", SelfRef)))
  )
)
val zero = nat.constructors(0)
val succ = nat.constructors(1)

lazy val pred = recFun(nat, nat) { self =>
  Case(zero):
    zero
  Case(succ, natPredN):
    natPredN
}

lazy val double = recFun(nat, nat) { self =>
  Case(zero):
    zero
  Case(succ, natDoubleN):
    succ * (succ * (self * natDoubleN))
}

private val natEndo = nat.term ->: nat.term

lazy val add = recFun(nat, natEndo) { self =>
  Case(zero):
    TypingHelpers.fun(natAddRight :: nat.term, natAddRight)
  Case(succ, natAddN):
    TypingHelpers.fun(
      natAddRight :: nat.term,
      succ * ((self * natAddN) * natAddRight)
    )
}

object Nat:
  export lisa.maths.SetTheory.Types.ADTv2.library.{nat, zero, succ, pred, double, add}
