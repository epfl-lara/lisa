package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class FunctionTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}

  test("function definitions require exhaustive cases") {
    val boolDemo = adt(
      name = "boolFunctionMissingCaseTest",
      constructors = Seq(
        ("tru", Seq.empty),
        ("fals", Seq.empty)
      )
    )
    val truDemo = boolDemo.constructors(0)
    val falsDemo = boolDemo.constructors(1)

    assertThrows[IllegalArgumentException] {
      fun(boolDemo, boolDemo):
        Case(truDemo):
          falsDemo
    }
  }

  test("function definitions reject wrong case arity") {
    val boolDemo = adt(
      name = "boolFunctionArityTest",
      constructors = Seq(
        ("tru", Seq.empty),
        ("fals", Seq.empty)
      )
    )
    val truDemo = boolDemo.constructors(0)
    val falsDemo = boolDemo.constructors(1)
    val x = variable[Ind]

    assertThrows[IllegalArgumentException] {
      fun(boolDemo, boolDemo):
        Case(truDemo, x):
          falsDemo
        Case(falsDemo):
          truDemo
    }
  }
}
