package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

private val listLengthHead = variable[Ind]
private val listLengthTail = variable[Ind]

val list = adt(
  name = "list",
  typeVars = "A",
  constructors =
    Seq(("nil", Seq.empty), ("cons", Seq(("head", "A"), ("tail", SelfRef))))
)
val nil = list.constructors(0)
val cons = list.constructors(1)

lazy val length = recFun(list, nat) { self =>
  Case(nil):
    zero
  Case(cons, listLengthHead, listLengthTail):
    succ * (self * listLengthTail)
}

object List:
  export lisa.maths.SetTheory.Types.ADTv2.library.{list, nil, cons, length}
