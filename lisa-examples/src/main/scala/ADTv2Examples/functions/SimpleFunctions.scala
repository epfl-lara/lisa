package ADTv2Examples.functions

import lisa.maths.SetTheory.Types.ADTv2.*

object SimpleFunctions extends lisa.Main {

  val unitDemo = adt(
    name = "unitFunDemo",
    constructors = Seq(
      ("star", Seq.empty)
    )
  )
  val starDemo = unitDemo.constructors(0)

  val idUnit = fun(unitDemo, unitDemo):
    Case(starDemo):
      starDemo

  section("Simple pattern-defined function")
  show(idUnit.intro)
  show(idUnit.elim(starDemo))
}
