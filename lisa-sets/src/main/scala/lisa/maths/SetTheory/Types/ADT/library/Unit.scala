package lisa.maths.SetTheory.Types.ADT.library

import lisa.maths.SetTheory.Types.ADT._

val unit = adt(
  name = "unit",
  constructors = Seq(
    ("star", Seq.empty)
  )
)
val star = unit.constructors(0)

object Unit:
  export lisa.maths.SetTheory.Types.ADT.library.{unit, star}
