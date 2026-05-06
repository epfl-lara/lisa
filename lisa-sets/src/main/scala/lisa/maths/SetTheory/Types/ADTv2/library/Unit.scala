package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.Types.ADTv2.*

val unit = adt(
  name = "unit",
  constructors = Seq(
    ("star", Seq.empty)
  )
)
val star = unit.constructors(0)

object Unit:
  export lisa.maths.SetTheory.Types.ADTv2.library.{unit, star}
