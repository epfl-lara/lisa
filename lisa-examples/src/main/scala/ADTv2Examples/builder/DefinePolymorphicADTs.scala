package ADTv2Examples.builder

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object DefinePolymorphicADTs extends lisa.Main {

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
  show(boxDemo.induction)
  show(listDemo.induction)
  show(listDemo.elim)
  show(unionDemo.induction)
  show(unionDemo.injectivity(inlDemo, inrDemo))

  section("Constructor theorems")
  show(packDemo.intro)
  show(packDemo.introApp)
  show(consDemo.intro)
  show(consDemo.introApp)
  show(nilDemo.intro)
}
