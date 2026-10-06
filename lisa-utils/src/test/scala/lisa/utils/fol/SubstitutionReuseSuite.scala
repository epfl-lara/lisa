package lisa.utils.fol

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionReuseSuite extends AnyFunSuite:
  private val x = variable[Ind](K.Identifier("reuse-x"))
  private val y = variable[Ind](K.Identifier("reuse-y"))
  private val z = variable[Ind](K.Identifier("reuse-z"))
  private val f = variable[Ind >>: Ind](K.Identifier("reuse-f"))
  private def argument(e: Expr[Ind]): Expr[Ind] = e.asInstanceOf[App[Ind, Ind]].arg

  test("retain unchanged applications without changing their value"):
    val term = f(f(x))
    val result = term.substitute(y := z)
    assert(result == term)
    assert(result eq term)

  test("replace changed children and leave the original immutable"):
    val term = f(x)
    val result = term.substitute(x := y)
    assert(argument(result) eq y)
    assert(argument(term) eq x)
    assert(!(result eq term))

  test("retain unchanged abstractions only on the non-capture branch"):
    val term = λ(x, f(x))
    val result = term.substitute(y := z)
    assert(result == term)
    assert(result eq term)
    val capturing = λ(x, f(y)).substitute(y := x)
    assert(capturing.v.id != x.id)
    assert(capturing.freeVars.contains(x))

  test("visit virtual substitution even for empty maps"):
    var visits = 0
    class VisitingVariable extends Variable[Ind](K.Identifier("reuse-visited")):
      override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Expr[Ind] =
        visits += 1
        y
    val term = f(new VisitingVariable)
    val result = term.substituteUnsafe(Map.empty)
    assert(visits == 1)
    assert(argument(result) eq y)

  test("do not rewrite inserted replacements in simultaneous substitution"):
    val result = f(x).substitute(x := y, y := z)
    assert(argument(result) eq y)

  test("keep public sort checks even for irrelevant replacements"):
    val term = f(x)
    intercept[IllegalArgumentException]:
      term.substituteWithCheck(Map(y -> variable[Prop](K.Identifier("reuse-prop"))))

  test("observe overridden application substitution"):
    var visits = 0
    class VisitingApplication extends App[Ind, Ind](f, x):
      override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): App[Ind, Ind] =
        visits += 1
        super.substituteUnsafe(m)
    val inner = new VisitingApplication
    val result = f(inner).substitute(y := z)
    assert(visits == 1)
    assert(result == f(inner))
