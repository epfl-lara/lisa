package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.Types.ADTv2._

val box = adt(
  name = "box",
  typeVars = "A",
  constructors = Seq(
    ("pack", Seq(("x", "A")))
  )
)
val pack = box.constructors(0)

object Box:
  export lisa.maths.SetTheory.Types.ADTv2.library.{box, pack}
