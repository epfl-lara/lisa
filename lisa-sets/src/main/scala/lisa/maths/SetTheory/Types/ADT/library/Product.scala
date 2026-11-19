package lisa.maths.SetTheory.Types.ADT.library

import lisa.maths.SetTheory.Types.ADT._

val product = adt(
  name = "product",
  typeVars = ("A", "B"),
  constructors = Seq(
    ("pair", Seq(("x", "A"), ("y", "B")))
  )
)
val pair = product.constructors(0)

object Product:
  export lisa.maths.SetTheory.Types.ADT.library.{product, pair}
