package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class RecFunctionTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*

  test("double recursion exposes succ equation") {
    assert(double.intro.statement != null)
    assert(double.elim.contains(zero))
    assert(double.elim.contains(succ))
  }

  test("polymorphic list recursion specializes to nat lists") {
    val lengthNat = length.specialize(nat)
    val nilNat = nil.specialize(nat)
    assert(lengthNat.intro.statement != null)
    assert(lengthNat.elim.contains(nilNat))
  }

  test("higher-order recursive add is usable with typecheck") {
    assert(add.intro.statement != null)
    assert(add.introApp.statement != null)
    assert(add.elim.contains(zero))
    assert(add.elim.contains(succ))
  }

  test("recursive definitions require exhaustive cases") {
    val boolDemo = adt(
      name = "boolRecFunctionMissingCaseTest",
      constructors = Seq(
        ("tru", Seq.empty),
        ("fals", Seq.empty)
      )
    )
    val truDemo = boolDemo.constructors(0)

    assertThrows[IllegalArgumentException] {
      recFun(boolDemo, boolDemo) { self =>
        Case(truDemo):
          truDemo
      }
    }
  }
}
