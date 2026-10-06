package lisa.hol

import lisa.hol.VarsAndFunctions.*
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class TypedSubstitutionReuseSuite extends AnyFunSuite:
  private val a = TypeVariable(K.Identifier("reuse-type-A"))
  private val b = TypeVariable(K.Identifier("reuse-type-B"))
  private val x = TypedVariable(K.Identifier("reuse-typed-x"), a)
  private val y = TypedVariable(K.Identifier("reuse-typed-y"), a)
  private val f = variable[Ind >>: Ind](K.Identifier("reuse-typed-f"))
  private def argument(e: Expr[Ind]): Expr[Ind] = e.asInstanceOf[App[Ind, Ind]].arg

  test("retain a typed variable whose annotation is unchanged"):
    val result = x.substitute(y := x)
    assert(result.asInstanceOf[TypedVariable].typ eq a)
    assert(result eq x)

  test("retain an application with unchanged annotated children"):
    val term = f(x)
    val result = term.substitute(y := x)
    assert(argument(result).asInstanceOf[TypedVariable].typ eq a)
    assert(result eq term)

  test("preserve annotation-only changes despite equal kernel expressions"):
    val term = f(x)
    val result = term.substitute(a := b)
    assert(result.underlying == term.underlying)
    assert(!(result eq term))
    assert(argument(result).asInstanceOf[TypedVariable].typ eq b)
    assert(x.typ eq a)

  test("preserve a supplied replacement with the same erased identity"):
    val replacement = TypedVariable(x.id, b)
    val term = f(x)
    val result = term.substitute(x := replacement)
    assert(result.underlying == term.underlying)
    assert(argument(result) eq replacement)

  test("keep inserted annotation unchanged under simultaneous substitution"):
    val result = f(y).substitute(y := x, a := b)
    assert(argument(result) eq x)
    assert(argument(result).asInstanceOf[TypedVariable].typ eq a)

  test("retain changed annotations beneath an unchanged binder"):
    val bound = variable[Ind](K.Identifier("reuse-binder"))
    val term = λ(bound, f(x))
    val result = term.substitute(a := b)
    assert(result.underlying == term.underlying)
    assert(!(result eq term))
    assert(result.body.asInstanceOf[App[Ind, Ind]].arg.asInstanceOf[TypedVariable].typ eq b)

  test("compare annotation identity rather than its erased equality"):
    val oldType = TypedVariable(K.Identifier("reuse-annotated-type"), a)
    val newType = TypedVariable(oldType.id, b)
    val term = TypedVariable(K.Identifier("reuse-nested-annotation"), oldType)
    val result = term.substitute(oldType := newType).asInstanceOf[TypedVariable]
    assert(oldType == newType)
    assert(!(result eq term))
    assert(result.typ eq newType)
