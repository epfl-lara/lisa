package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class BasicsSmokeTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*

  test("basic library functions expose core equations") {
    assert(not.elim(tru).statement != null)
    assert(not.elim(fals).statement != null)
    assert(double.elim(zero).statement != null)
    assert(double.elim(succ).statement != null)
    assert(length.elim(nat)(nil).statement != null)
  }

  test("package wildcard import keeps library terms directly usable") {
    assert(add.intro.statement != null)
    assert(add.introApp.statement != null)
    assert(unit.term != null)
    assert(list(nat) != null)
  }
}
