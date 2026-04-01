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

  test("ADT v2 polymorphic list induction is usable") {
    val nat = API.defineAST(
      name = "natForInductionSmoke",
      typeVars = Seq.empty,
      constructors = Seq(
        ("zero", Seq.empty),
        ("succ", Seq(("k", SelfRef)))
      )
    )
    val zero = nat.constructors(0)
    val succ = nat.constructors(1)

    val list = API.defineAST(
      name = "listForInductionSmoke",
      typeVars = Seq("A"),
      constructors = Seq(
        ("nil", Seq.empty),
        ("cons", Seq(("head", "A"), ("tail", SelfRef)))
      )
    )
    val nil = list.constructors(0)
    val cons = list.constructors(1)

    val x, head, tail = variable[Ind]

    Theorem((x :: list) |- x === x) {
      have(thesis) by Induction(x, list) {
        Case(nil) subproof {
          have(thesis) by RightRefl
        }
        Case(cons, head, tail) subproof {
          have(thesis) by RightRefl
        }
      }
    }
  }

  test("ADT v2 regression: constructor arg name x does not capture induction variable") {
    val nat = API.defineAST(
      name = "natForCaptureSmoke",
      typeVars = Seq.empty,
      constructors = Seq(
        ("zero", Seq.empty),
        ("succ", Seq(("k", SelfRef)))
      )
    )

    val listX = API.defineAST(
      name = "listCaptureRegression",
      typeVars = Seq("A"),
      constructors = Seq(
        ("nil", Seq.empty),
        ("cons", Seq(("x", "A"), ("xs", SelfRef)))
      )
    )

    val nil = listX.constructors(0)
    val cons = listX.constructors(1)
    val x, elem, xs = variable[Ind]

    Theorem((x :: listX) |- x === x) {
      have(thesis) by Induction(x, listX) {
        Case(nil) subproof {
          have(thesis) by RightRefl
        }
        Case(cons, elem, xs) subproof {
          have(thesis) by RightRefl
        }
      }
    }
  }

  test("ADT v2 recursive functions over polymorphic list expose expected eliminations") {
    val hd, tl, k = variable[Ind]

    val list = API.defineAST(
      name = "listForRecursiveSmoke",
      typeVars = Seq("A"),
      constructors = Seq(
        ("nil", Seq.empty),
        ("cons", Seq(("head", "A"), ("tail", SelfRef)))
      )
    )
    val nil = list.constructors(0)
    val cons = list.constructors(1)

    val nat = API.defineAST(
      name = "natForRecursiveSmoke",
      typeVars = Seq.empty,
      constructors = Seq(
        ("zero", Seq.empty),
        ("succ", Seq(("k", SelfRef)))
      )
    )
    val zero = nat.constructors(0)
    val succ = nat.constructors(1)

    val length = recFun(list, nat) { self =>
      Case(nil):
        zero
      Case(cons, hd, tl):
        succ * (self * tl)
    }
    val listTypeParam = length.typeVariables.toSeq.head
    val lengthNat = length.term.substitute(listTypeParam := nat())

    val listFromLength = recFun(nat, list) { self =>
      Case(zero):
        nil * nat()
      Case(succ, k):
        cons * nat() * zero * (self * k)
    }

    Theorem(() |- listFromLength * zero === nil * nat()) {
      have(thesis) by Restate.from(listFromLength.elim(zero))
    }

    Theorem((k :: nat) |- listFromLength * (succ * k) === cons * nat() * zero * (listFromLength * k)) {
      have(thesis) by Restate.from(listFromLength.elim(succ))
    }

    Theorem(() |- lengthNat * (nil * nat()) === zero) {
      have(thesis) by Tautology.from(length.elim(nil) of (listTypeParam := nat()))
    }
  }
}
