package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class SpecializationTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*

  test("specialized constructors stay usable") {
    val packUnit = pack.specialize(unit)
    assert(packUnit.intro.statement != null)
    assert(packUnit.introApp.statement != null)
  }

  test("specialized recursive functions expose expected eliminations") {
    val lengthNat = length.specialize(nat)
    val nilNat = nil.specialize(nat)
    assert(lengthNat.intro.statement != null)
    assert(lengthNat.elim.contains(nilNat))
  }

  test("substitute and specialize agree on terms") {
    val boxViaSubst = box.substitute(box.typeVariablesSeq.head := unit)
    val boxViaSpecialize = box.specialize(unit)

    assert(boxViaSubst.term == boxViaSpecialize.term)
  }
}
