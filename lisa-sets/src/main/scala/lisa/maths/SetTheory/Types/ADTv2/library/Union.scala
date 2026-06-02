package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.*

private val unionLeft = variable[Ind]
private val unionRight = variable[Ind]

val union = adt(
  name = "union",
  typeVars = ("A", "B"),
  constructors = Seq(
    ("inl", Seq(("x", "A"))),
    ("inr", Seq(("y", "B")))
  )
)
val inl = union.constructors(0)
val inr = union.constructors(1)

lazy val isLeft = recFun(union, bool) { self =>
  Case(inl, unionLeft):
    tru
  Case(inr, unionRight):
    fals
}

object Union:
  export lisa.maths.SetTheory.Types.ADTv2.library.{union, inl, inr, isLeft}
