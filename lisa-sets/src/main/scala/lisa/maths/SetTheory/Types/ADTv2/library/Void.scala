package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.Types.ADTv2.*

val void = adt(
  name = "void",
  constructors = Seq.empty
)

object Void:
  export lisa.maths.SetTheory.Types.ADTv2.library.{void}
