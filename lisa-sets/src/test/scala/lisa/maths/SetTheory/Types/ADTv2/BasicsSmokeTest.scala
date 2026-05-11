package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class BasicsSmokeTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*

  test("basic library functions expose core equations") {
    assert(not.elim.contains(tru))
    assert(not.elim.contains(fals))
    assert(double.elim.contains(zero))
    assert(double.elim.contains(succ))
    assert(length.elim(nat).contains(nil))
  }

  test("package wildcard import keeps library terms directly usable") {
    assert(add.intro.statement != null)
    assert(add.introApp.statement != null)
    assert(unit.term != null)
    assert(list(nat) != null)
  }
}
