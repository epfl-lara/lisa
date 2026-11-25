package lisa.maths.SetTheory.Types.ADT.library

import lisa.maths.SetTheory.Types.ADT._

val void = adt(
  name = "void",
  constructors = Seq.empty
)

object Void:
  export lisa.maths.SetTheory.Types.ADT.library.{void}
