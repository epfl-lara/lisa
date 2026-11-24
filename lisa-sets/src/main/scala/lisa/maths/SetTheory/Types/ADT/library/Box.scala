package lisa.maths.SetTheory.Types.ADT.library

import lisa.maths.SetTheory.Types.ADT._

val box = adt(
  name = "box",
  typeVars = "A",
  constructors = Seq(
    ("pack", Seq(("x", "A")))
  )
)
val pack = box.constructors(0)

object Box:
  export lisa.maths.SetTheory.Types.ADT.library.{box, pack}
