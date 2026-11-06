package lisa.kernel

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class AlphaInvariantFormSuite extends AnyFunSuite:
  private val x = Variable(Identifier("x"), Ind)
  private val y = Variable(Identifier("y"), Ind)
  private val p = Constant(Identifier("P"), Ind -> Prop)
  private val r = Constant(Identifier("R"), Ind -> (Ind -> Prop))
  private val q = Constant(Identifier("q"), Prop)

  test("alpha-renamed binders have equal simple forms and hash-set membership"):
    val pairs = Seq(
      forall(Lambda(x, p(x))) -> forall(Lambda(y, p(y))),
      Lambda(x, r(x)(x)) -> Lambda(y, r(y)(y))
    )
    pairs.foreach: (left, right) =>
      val l = simpleReducedForm(left)
      val rr = simpleReducedForm(right)
      assert(l == rr)
      assert(l.hashCode == rr.hashCode)
      assert(Set(l).contains(rr))

  test("vacuous binders retain their sort in equality"):
    val a = Variable(x.id, Prop)
    val left = Lambda(x, q)
    val right = Lambda(a, q)
    assert(simpleReducedForm(left) != simpleReducedForm(right))
    assert(!isSame(left, right))

  test("locally nameless conversion distinguishes same-named variables at different sorts"):
    val a = Variable(x.id, Prop)
    val b = Variable(y.id, Prop)
    assert(simpleReducedForm(Lambda(a, and(a)(p(x)))) == simpleReducedForm(Lambda(b, and(b)(p(x)))))
    assert(simpleReducedForm(Lambda(x, p(x))) != simpleReducedForm(Lambda(y, p(x))))

  test("lambda reuse retains reconstruction metadata"):
    val body = SimpleConstant(q.id, Prop, true)
    val lambda = SimpleLambda(Ind, body)(x)
    assert(toLocallyNameless(lambda) eq lambda)
    assert(fromLocallyNameless(lambda, Map.empty, 0) eq lambda)
    assert(computeNormalForm(lambda) eq lambda)
    assert(isSame(toExpressionAIG(lambda), Lambda(x, q)))

  test("quantifier inversion retains reconstruction metadata"):
    val formula = forall(Lambda(x, p(x)))
    val original = simpleReducedForm(formula)
    val inverse = getInversePolar(original)
    assert(getInversePolar(inverse) == original)
    assert(isSame(toExpressionAIG(fromLocallyNameless(inverse, Map.empty, 0)), neg(formula)))
