package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class RecFunctionTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*

  test("double recursion exposes succ equation") {
    assert(double.intro.statement != null)
    assert(double.elim(zero).statement != null)
    assert(double.elim(succ).statement != null)
  }

  test("polymorphic list recursion specializes to nat lists") {
    assert(length.intro(nat).statement != null)
    assert(length.elim(nat)(nil).statement != null)
  }

  test("higher-order recursive add is usable with typecheck") {
    assert(add.intro.statement != null)
    assert(add.introApp.statement != null)
    assert(add.elim(zero).statement != null)
    assert(add.elim(succ).statement != null)
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
