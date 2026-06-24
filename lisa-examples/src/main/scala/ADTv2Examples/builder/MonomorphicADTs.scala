package ADTv2Examples.builder

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

object MonomorphicADTs extends lisa.Main {

  val boolDemo = adt(
    name = "boolDemo",
    constructors = Seq(
      ("tru", Seq.empty),
      ("fals", Seq.empty)
    )
  )
  val truDemo = boolDemo.constructors(0)
  val falsDemo = boolDemo.constructors(1)

  val natDemo = adt(
    name = "natDemo",
    constructors = Seq(
      ("zero", Seq.empty),
      ("succ", Seq(("k", SelfRef)))
    )
  )
  val zeroDemo = natDemo.constructors(0)
  val succDemo = natDemo.constructors(1)

  val voidDemo = adt(
    name = "voidDemo",
    constructors = Seq.empty
  )

  section("ADT theorems")
  show(boolDemo.induction)
  show(boolDemo.elim)
  show(boolDemo.disjointness(truDemo, falsDemo))
  show(natDemo.induction)
  show(natDemo.elim)
  show(voidDemo.elim)

  section("Constructor theorems")
  show(zeroDemo.intro)
  show(succDemo.intro)
  show(succDemo.introApp)
}
