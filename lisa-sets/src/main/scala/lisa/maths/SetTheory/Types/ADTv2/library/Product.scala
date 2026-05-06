package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.Types.ADTv2.*

val product = adt(
  name = "product",
  typeVars = ("A", "B"),
  constructors = Seq(
    ("pair", Seq(("x", "A"), ("y", "B")))
  )
)
val pair = product.constructors(0)

object Product:
  export lisa.maths.SetTheory.Types.ADTv2.library.{product, pair}
