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

  val boolDemo = adt(
    name = "boolFunDemo",
    constructors = Seq(
      ("tru", Seq.empty),
      ("fals", Seq.empty)
    )
  )
  val truDemo = boolDemo.constructors(0)
  val falsDemo = boolDemo.constructors(1)

  val idUnit = fun(unitDemo, unitDemo):
    Case(starDemo):
      starDemo

  val flipBool = fun(boolDemo, boolDemo):
    Case(truDemo):
      falsDemo
    Case(falsDemo):
      truDemo

  val squashBoolToUnit = fun(boolDemo, unitDemo):
    Case(truDemo):
      starDemo
    Case(falsDemo):
      starDemo

  section("Unit function")
  show(idUnit.intro)
  show(idUnit.elim(starDemo))

  section("Boolean endomorphism")
  show(flipBool.intro)
  show(flipBool.elim(truDemo))
  show(flipBool.elim(falsDemo))

  section("Boolean to unit")
  show(squashBoolToUnit.intro)
  show(squashBoolToUnit.elim(truDemo))
  show(squashBoolToUnit.elim(falsDemo))
}
