package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class ADTv2Test extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.Types.ADTv2
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.SetTheory.{*, given}

  private val bool = API.defineAST(
    name = "bool",
    typeVars = Seq.empty,
    constructors = Seq(
      ("tru", Seq.empty),
      ("fals", Seq.empty)
    )
  )

  private val tru = bool.constructors(0)
  private val fals = bool.constructors(1)
  private val b = variable[Ind]

  private val notFun = fun(bool, bool):
    Case(tru):
      fals
    Case(fals):
      tru

  test("ADT v2 injectivity for distinct constructors") {
    Theorem(() |- !(tru === fals)) {
      have(thesis) by Tautology.from(bool.injectivity(tru, fals))
    }
  }

  test("ADT v2 function elimination theorem") {
    Theorem(() |- notFun * tru === fals) {
      have(thesis) by Tautology.from(notFun.elim(tru))
    }
  }

  test("ADT v2 function involution by induction") {
    Theorem((b :: bool) |- notFun * (notFun * b) === b) {
      val notFalse = have(notFun * fals === tru) by Restate.from(notFun.elim(fals))
      val notTrue = have(notFun * tru === fals) by Restate.from(notFun.elim(tru))

      have(thesis) by Induction(b, bool) {
        Case(tru) subproof {
          have(notFun * (notFun * tru) === tru) by Congruence.from(notTrue, notFalse)
        }
        Case(fals) subproof {
          have(notFun * (notFun * fals) === fals) by Congruence.from(notTrue, notFalse)
        }
      }
    }
  }
}
