package lisa.maths.SetTheory.Types.ADT.library

import lisa.maths.SetTheory.Types.ADT._

val option = adt(
  name = "option",
  typeVars = "T",
  constructors = Seq(
    ("some", Seq(("x", "T"))),
    ("none", Seq.empty)
  )
)
val some = option.constructors(0)
val none = option.constructors(1)

object Option:
  export lisa.maths.SetTheory.Types.ADT.library.{option, some, none}
