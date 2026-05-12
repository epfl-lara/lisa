package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class RegressionTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

  test("constructor argument name x does not capture induction variable") {
    val listCapture = adt(
      name = "listCaptureRegressionTest",
      typeVars = "A",
      constructors = Seq(
        ("nil", Seq.empty),
        ("cons", Seq(("x", "A"), ("xs", SelfRef)))
      )
    )

    val nilCapture = listCapture.constructors(0)
    val consCapture = listCapture.constructors(1)
    val T = variable[Ind]
    assert(listCapture.induction(T).statement != null)
    assert(listCapture.elim(T).statement != null)
    assert(listCapture.injectivity(consCapture, nilCapture, T).statement != null)
  }
}
