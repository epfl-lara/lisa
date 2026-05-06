package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class InductionTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.library.*
  import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

  test("boolean involution can be proved by induction") {
    val b = variable[Ind]

    Theorem((b :: bool) |- not * (not * b) === b) {
      val negFalse = have(not * fals === tru) by Restate.from(not.elim(fals))
      val negTrue = have(not * tru === fals) by Restate.from(not.elim(tru))

      have(thesis) by Induction(b, bool) {
        Case(tru) subproof {
          have(not * (not * tru) === tru) by Congruence.from(negTrue, negFalse)
        }
        Case(fals) subproof {
          have(not * (not * fals) === fals) by Congruence.from(negTrue, negFalse)
        }
      }
    }
  }

  test("polymorphic list induction is usable") {
    val listLocal = adt(
      name = "listInductionTest",
      typeVars = "A",
      constructors = Seq(
        ("nil", Seq.empty),
        ("cons", Seq(("head", "A"), ("tail", SelfRef)))
      )
    )
    val nilLocal = listLocal.constructors(0)
    val consLocal = listLocal.constructors(1)

    assert(listLocal.induction.statement != null)
    assert(listLocal.elim.statement != null)
    assert(listLocal.injectivity(consLocal, nilLocal).statement != null)
  }
}
