package lisa.kernel

import lisa.kernel.fol.FOL._
import org.scalatest.funsuite.AnyFunSuite

class PolarizeFlatteningSuite extends AnyFunSuite {
  private val enabled = sys.props.get("lisa.ol.flatten").fold(true)(_.toBoolean)
  private val p = Variable(Identifier("flatten-p"), Prop)
  private val q = Variable(Identifier("flatten-q"), Prop)
  private val r = Variable(Identifier("flatten-r"), Prop)

  private def binary(e: Expression, positive: Boolean): SimpleExpression = e match {
    case neg(a) => binary(a, !positive)
    case and(a, b) => SimpleAnd(Seq(binary(a, true), binary(b, true)), positive)
    case or(a, b) => SimpleAnd(Seq(binary(a, false), binary(b, false)), !positive)
    case _ => polarize(e, positive)
  }

  private def checkShape(e: Expression, polarity: Boolean, children: Int): Unit = {
    val result = polarize(e, true).asInstanceOf[SimpleAnd]
    assert(result.polarity == polarity)
    assert(result.children.size == (if (enabled) children else 2))
    if (enabled) assert(!result.children.exists {
      case SimpleAnd(_, true) => true
      case _ => false
    })
    assert(polarize(e, true) eq result)
    val inverse = polarize(e, false).asInstanceOf[SimpleAnd]
    assert(inverse.polarity != polarity)
    assert(inverse.children == result.children)
  }

  test("flatten associative conjunctions and disjunctions in either orientation") {
    checkShape(and(and(p)(q))(r), true, 3)
    checkShape(and(p)(and(q)(r)), true, 3)
    checkShape(or(or(p)(q))(r), false, 3)
    checkShape(or(p)(or(q)(r)), false, 3)
  }

  test("flatten through De Morgan duals but retain opposite-polarity groups") {
    val expression = and(p)(neg(or(q)(neg(r))))
    checkShape(expression, true, 3)
    if (enabled) {
      val children = polarize(expression, true).asInstanceOf[SimpleAnd].children
      assert(children == Seq(polarize(p, true), polarize(q, false), polarize(r, true)))
    }
    val mixed = polarize(and(p)(or(q)(r)), true).asInstanceOf[SimpleAnd]
    assert(mixed.children.size == 2)
    assert(mixed.children(1).asInstanceOf[SimpleAnd].polarity == false)
    val unfolded = and(p)(neg(implies(q)(or(p)(r))))
    checkShape(unfolded, true, 4)
    if (enabled) assert(polarize(unfolded, true).asInstanceOf[SimpleAnd].children ==
      Seq(polarize(p, true), polarize(q, true), polarize(p, false), polarize(r, false)))
  }

  test("retain quantified scope and normalize formulas embedded in terms") {
    val x = Variable(Identifier("flatten-x"), Ind)
    val pred = Constant(Identifier("flatten-P"), Ind -> Prop)
    val quantified = forall(Lambda(x, and(pred(x))(and(q)(r))))
    val outer = polarize(and(p)(quantified), true).asInstanceOf[SimpleAnd]
    assert(outer.children.size == 2)
    assert(outer.children(1).isInstanceOf[SimpleForall])
    assert(isSame(quantified, forall(Lambda(x, and(and(r)(pred(x)))(q)))))
    val f = Constant(Identifier("flatten-f"), Prop -> Ind)
    assert(isSame(f(and(p)(and(q)(r))), f(and(and(r)(p))(q))))
    assert(!isSame(f(and(p)(q)), f(and(p)(r))))
    assert(isSame(and(p)(and(implies(p)(q))(neg(p))), bot))
  }

  test("agree with binary polarization on generated positive and negative formulas") {
    val atoms = Vector[Expression](p, q, r, top, bot)
    val pairs = for (a <- atoms; b <- atoms; op <- Vector(and, or)) yield op(a)(b)
    val inputs = pairs ++ (for (pair <- pairs; atom <- atoms) yield and(pair)(neg(or(atom)(pair))))
    for (e <- inputs; positive <- Vector(true, false)) {
      val expected = computeNormalForm(toLocallyNameless(binary(e, positive)))
      val actual = computeNormalForm(toLocallyNameless(polarize(e, positive)))
      assert(latticesEQ(actual, expected), s"$e, polarity=$positive")
    }
  }

  test("retain duplicate occurrences and reduce a longer chain") {
    val repeated = and(p)(and(p)(q))
    checkShape(repeated, true, 3)
    val chain = (1 to 128).foldLeft(p: Expression)((acc, _) => and(acc)(p))
    checkShape(chain, true, 129)
    assert(isSame(chain, p))
  }

  test("flatten deep left- and right-associated chains without recursive descent") {
    if (enabled) {
      val depth = 20000
      for (op <- Vector(and, or)) {
        val left = (1 to depth).foldLeft(p: Expression)((acc, _) => op(acc)(q))
        val right = (1 to depth).foldLeft(p: Expression)((acc, _) => op(q)(acc))
        checkShape(left, op == and, depth + 1)
        checkShape(right, op == and, depth + 1)
      }
    }
  }
}
