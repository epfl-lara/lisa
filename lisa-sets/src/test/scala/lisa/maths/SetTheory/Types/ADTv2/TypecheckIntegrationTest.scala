package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class TypecheckIntegrationTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*
  import lisa.maths.SetTheory.Types.Tactics.Typecheck
  import lisa.maths.SetTheory.Functions.Pi.{->:}

  test("constructor and recursive-function heads typecheck") {
    assert(Typecheck != null)
    assert((zero :: nat) != null)
    assert((succ :: (nat ->: nat)) != null)
    assert((double :: (nat ->: nat)) != null)
    assert((not :: (bool ->: bool)) != null)
  }

  test("nested nat terms typecheck") {
    val n = variable[Ind]
    assert(((n :: nat) |- succ * (double * n) :: nat) != null)
  }

  test("nested bool terms typecheck") {
    val b = variable[Ind]
    assert(((b :: bool) |- not * (not * b) :: bool) != null)
  }
}
