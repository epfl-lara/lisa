package lisa.maths.SetTheory.Types.ADT.library

import lisa.maths.SetTheory.Types.ADT._

val bool = adt(
  name = "bool",
  constructors = Seq(
    ("tru", Seq.empty),
    ("fals", Seq.empty)
  )
)
val tru = bool.constructors(0)
val fals = bool.constructors(1)

lazy val not = recFun(bool, bool) { _ =>
  Case(tru):
    fals
  Case(fals):
    tru
}

object Bool:
  export lisa.maths.SetTheory.Types.ADT.library.{bool, tru, fals, not}
