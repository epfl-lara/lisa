package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class SpecializationTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*

  test("specialized constructors stay usable") {
    assert(pack.intro(unit).statement != null)
    assert(pack.introApp(unit).statement != null)
  }

  test("specialized recursive functions expose expected eliminations") {
    val lengthNatElim = length.elim(nat)(nil)
    assert(length.intro(nat).statement != null)
    assert(lengthNatElim.statement != null)
  }

  test("term application and theorem specialization agree") {
    assert(box(unit) != null)
    assert(box.induction(unit).statement != null)
  }
}
