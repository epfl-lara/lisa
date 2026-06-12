package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.Types.ADTv2.*

val bool = adt(
  name = "bool",
  constructors = Seq(
    ("tru", Seq.empty),
    ("fals", Seq.empty)
  )
)
val tru = bool.constructors(0)
val fals = bool.constructors(1)

lazy val not = recFun(bool, bool) { self =>
  Case(tru):
    fals
  Case(fals):
    tru
}

object Bool:
  export lisa.maths.SetTheory.Types.ADTv2.library.{bool, tru, fals, not}
