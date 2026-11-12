package lisa.kernel

import lisa.kernel.fol.FOL._
import org.scalatest.funsuite.AnyFunSuite

class NormalizationCacheSuite extends AnyFunSuite:
  private val x = Variable(Identifier("normal-x"), Ind)
  private val y = Variable(Identifier("normal-y"), Ind)
  private val f = Constant(Identifier("normal-f"), Ind -> Ind)

  test("retain already-normal expressions and cache contractions independently"):
    for expression <- Seq(x, f, f(x), Lambda(x, f(y))) do
      assert(expression.isBetaNormal)
      assert(expression.betaNormalForm eq expression)
    val beta = Lambda(x, f(x))(y)
    val eta = Lambda(x, f(x))
    assert(!beta.isBetaNormal && !eta.isBetaNormal)
    assert(isSame(beta.betaNormalForm, f(y)))
    assert(eta.betaNormalForm == f)

  test("normalize below binders and avoid capture"):
    val expression = Lambda(x, Lambda(y, x))(y)
    val bound = Variable(Identifier("normal-fresh"), Ind)
    assert(!expression.isBetaNormal)
    assert(isSame(expression.betaNormalForm, Lambda(bound, y)))
    assert(!isSame(expression.betaNormalForm, Lambda(y, y)))
    assert(expression.betaNormalForm.freeVariables == Set(y))

  test("reuse unchanged application children when normalizing either operand"):
    val g = Variable(Identifier("normal-function"), Ind -> Ind)
    val expressions = Seq(f(Lambda(y, y)(x)), Lambda(g, g)(f)(x))
    for expression <- expressions do
      val normal = expression.betaNormalForm.asInstanceOf[Application]
      assert(!expression.isBetaNormal)
      assert(!(normal eq expression))
      assert(normal.f eq f)
      assert(normal.arg eq x)
      assert(normal.betaNormalForm eq normal)

  test("retain the eta side condition and normalize an eta redex exposed by beta reduction"):
    val binary = Constant(Identifier("normal-binary"), Ind -> (Ind -> Ind))
    val normal = Lambda(x, binary(x)(x))
    assert(normal.isBetaNormal && (normal.betaNormalForm eq normal))
    val expression = Lambda(x, Lambda(y, f(y))(x))
    assert(!expression.isBetaNormal)
    assert(expression.betaNormalForm == f)

  test("recompute normality when substitution reconstructs terms or introduces redexes"):
    val g = Variable(Identifier("normal-g"), Ind -> Ind)
    val normal = g(x)
    val copied = substituteVariables(normal, Map.empty)
    assert(copied.isBetaNormal && (copied.betaNormalForm eq copied))
    val beta = substituteVariables(normal, Map(g -> Lambda(y, y)))
    assert(!beta.isBetaNormal && beta.betaNormalForm == x)
    val higherOrder = Constant(Identifier("normal-higher-order"), (Ind -> Ind) -> Ind)
    val eta = substituteVariables(higherOrder(g), Map(g -> Lambda(x, f(x))))
    assert(!eta.isBetaNormal && eta.betaNormalForm == higherOrder(f))

  test("normalize eta redexes exposed by reducing an abstraction body"):
    val expression = Lambda(x, Lambda(y, y)(f(x)))
    assert(!expression.isBetaNormal)
    assert(expression.betaNormalForm eq f)
    assert(expression.betaNormalForm.isBetaNormal)
    val z = Variable(Identifier("normal-z"), Ind)
    val binary = Constant(Identifier("normal-nested-binary"), Ind -> (Ind -> Ind))
    val nested = Lambda(x, Lambda(z, Lambda(y, y)(binary(x)(z))))
    assert(nested.betaNormalForm eq binary)
