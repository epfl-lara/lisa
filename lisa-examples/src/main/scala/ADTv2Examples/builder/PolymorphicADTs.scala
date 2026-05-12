package ADTv2Examples.builder

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

object PolymorphicADTs extends lisa.Main {

  val boxDemo = adt(
    name = "boxDemo",
    typeVars = "A",
    constructors = Seq(
      ("pack", Seq(("x", "A")))
    )
  )
  val packDemo = boxDemo.constructors(0)

  val listDemo = adt(
    name = "listDemo",
    typeVars = "A",
    constructors = Seq(
      ("nil", Seq.empty),
      ("cons", Seq(("head", "A"), ("tail", SelfRef)))
    )
  )
  val nilDemo = listDemo.constructors(0)
  val consDemo = listDemo.constructors(1)

  val unionDemo = adt(
    name = "unionDemo",
    typeVars = ("A", "B"),
    constructors = Seq(
      ("inl", Seq(("x", "A"))),
      ("inr", Seq(("y", "B")))
    )
  )
  val inlDemo = unionDemo.constructors(0)
  val inrDemo = unionDemo.constructors(1)

  section("ADT theorems")
  show(boxDemo.induction(unit))
  show(listDemo.induction(unit))
  show(listDemo.elim(unit))
  show(unionDemo.induction(unit, nat))
  show(unionDemo.injectivity(inlDemo, inrDemo, unit, nat))

  section("Constructor theorems")
  show(packDemo.intro(unit))
  show(packDemo.introApp(unit))
  show(consDemo.intro(unit))
  show(consDemo.introApp(unit))
  show(nilDemo.intro(unit))
}
