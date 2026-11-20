package lisa.kernel

import lisa.kernel.fol.FOL._
import org.scalatest.funsuite.AnyFunSuite

class NormalizationCacheSuite extends AnyFunSuite:
  private val x = Variable(Identifier("normal-x"), Ind)
  private val y = Variable(Identifier("normal-y"), Ind)
  private val f = Constant(Identifier("normal-f"), Ind -> Ind)

  test("retain normal atoms, applications, and abstractions as their own normal form"):
    for expression <- Seq(x, f, f(x), Lambda(x, f(y))) do
      assert(expression.isBetaNormal)
      assert(expression.betaNormalForm eq expression)

  test("cache beta and eta contractions with a false normality flag"):
    val beta = Lambda(x, f(x))(y)
    val eta = Lambda(x, f(x))
    assert(!beta.isBetaNormal)
    assert(isSame(beta.betaNormalForm, f(y)))
    assert(!eta.isBetaNormal)
    assert(eta.betaNormalForm == f)

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

  test("normalize inside both application operands and abstraction bodies"):
    val identity = Lambda(x, x)
    val expressions = Seq(f(identity(y)), Lambda(x, identity(f(y))))
    val expected = Seq(f(y), Lambda(x, f(y)))
    for (expression, normal) <- expressions.zip(expected) do
      assert(!expression.isBetaNormal)
      assert(isSame(expression.betaNormalForm, normal))
      assert(expression.betaNormalForm.isBetaNormal)

  test("avoid capture when a beta reduction substitutes a free variable under a binder"):
    val expression = Lambda(x, Lambda(y, x))(y)
    val bound = Variable(Identifier("normal-fresh"), Ind)
    assert(!expression.isBetaNormal)
    assert(isSame(expression.betaNormalForm, Lambda(bound, y)))
    assert(!isSame(expression.betaNormalForm, Lambda(y, y)))
    assert(expression.betaNormalForm.freeVariables == Set(y))

  test("do not eta-reduce a function containing the binding variable"):
    val binary = Constant(Identifier("normal-binary"), Ind -> (Ind -> Ind))
    val expression = Lambda(x, binary(x)(x))
    assert(expression.isBetaNormal)
    assert(expression.betaNormalForm eq expression)

  test("normalize eta redexes exposed by reducing an abstraction body"):
    val expression = Lambda(x, Lambda(y, y)(f(x)))
    assert(!expression.isBetaNormal)
    assert(expression.betaNormalForm eq f)
    assert(expression.betaNormalForm.isBetaNormal)
    val z = Variable(Identifier("normal-z"), Ind)
    val binary = Constant(Identifier("normal-nested-binary"), Ind -> (Ind -> Ind))
    val nested = Lambda(x, Lambda(z, Lambda(y, y)(binary(x)(z))))
    assert(nested.betaNormalForm eq binary)

  test("recompute normality when substitution creates beta and eta redexes"):
    val g = Variable(Identifier("normal-g"), Ind -> Ind)
    val normal = g(x)
    assert(normal.isBetaNormal)
    val copied = substituteVariables(normal, Map.empty)
    assert(copied.isBetaNormal)
    assert(copied.betaNormalForm eq copied)

    val beta = substituteVariables(normal, Map(g -> Lambda(y, y)))
    assert(!beta.isBetaNormal)
    assert(beta.betaNormalForm == x)

    val higherOrder = Constant(Identifier("normal-higher-order"), (Ind -> Ind) -> Ind)
    val application = higherOrder(g)
    assert(application.isBetaNormal)
    val eta = substituteVariables(application, Map(g -> Lambda(x, f(x))))
    assert(!eta.isBetaNormal)
    assert(eta.betaNormalForm == higherOrder(f))

  test("reuse applications and abstractions unchanged by substitution"):
    val z = Variable(Identifier("reuse-z"), Ind)
    val application = f(x)
    val abstraction = Lambda(y, application)
    for expression <- Seq(application, abstraction) do
      assert(substituteVariables(expression, Map.empty) eq expression)
      assert(substituteVariables(expression, Map(z -> x)) eq expression)
      assert(substituteVariables(expression, Map(x -> x)) eq expression)
    assert(substituteVariables(abstraction, Map(y -> z)) eq abstraction)

  test("reuse unaffected children when substituting into applications and abstractions"):
    val binary = Constant(Identifier("reuse-binary"), Ind -> (Ind -> Ind))
    val left = binary(x)
    val right = f(y)
    val application = left(right)

    val changedRight = substituteVariables(application, Map(y -> x)).asInstanceOf[Application]
    assert(!(changedRight eq application))
    assert(changedRight.f eq left)
    assert(changedRight.arg == f(x))

    val changedLeft = substituteVariables(application, Map(x -> y)).asInstanceOf[Application]
    assert(!(changedLeft eq application))
    assert(changedLeft.f == binary(y))
    assert(changedLeft.arg eq right)

    val abstraction = Lambda(x, application)
    val z = Variable(Identifier("reuse-body-z"), Ind)
    val changedAbstraction = substituteVariables(abstraction, Map(y -> z)).asInstanceOf[Lambda]
    assert(!(changedAbstraction eq abstraction))
    assert(changedAbstraction.v eq x)
    assert(changedAbstraction.body.asInstanceOf[Application].f eq left)

    val changedBody = substituteVariables(abstraction, Map(y -> f(x))).asInstanceOf[Lambda]
    assert(!(changedBody eq abstraction))
    assert(changedBody.v != x)
    assert(changedBody.freeVariables == Set(x))
    assert(isSame(changedBody, Lambda(changedBody.v, binary(changedBody.v)(f(f(x))))))
