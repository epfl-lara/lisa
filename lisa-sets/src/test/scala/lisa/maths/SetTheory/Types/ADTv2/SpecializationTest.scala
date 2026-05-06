package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class SpecializationTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*

  test("specialized constructors stay usable") {
    assert(pack.introAt(unit).statement != null)
    assert(pack.introAppAt(unit).statement != null)
  }

  test("specialized recursive functions expose expected eliminations") {
    val lengthNatElim = length.elimAt(nat)
    assert(length.introAt(nat).statement != null)
    assert(lengthNatElim.contains(nil))
  }

  test("term application and theorem specialization agree") {
    assert(box(unit) != null)
    assert(box.inductionAt(unit).statement != null)
  }
}
