package lisa.utils.fol

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class CaptureSuite extends AnyFunSuite:
  private val x = variable[Ind](K.Identifier("capture-x"))
  private val y = variable[Ind](K.Identifier("capture-y"))
  private val z = variable[Ind](K.Identifier("capture-z"))
  private val p = variable[Ind >>: Prop](K.Identifier("capture-p"))

  test("capture detection agrees with kernel substitution across nested binders"):
    val expressions = Seq[Expr[Prop]](p(x), forall(x, p(y)), forall(x, forall(y, p(z))),
      forall(x, forall(x, p(y))), forall(y, p(x)) /\ forall(x, p(z)))
    val maps = Seq(Map[Variable[?], Expr[?]](y -> x), Map[Variable[?], Expr[?]](x -> y, y -> z),
      Map[Variable[?], Expr[?]](z -> x, x -> y), Map.empty[Variable[?], Expr[?]])
    for expression <- expressions; substitutions <- maps do
      val front = expression.substituteUnsafe(substitutions)
      val kernel = K.substituteVariables(expression.underlying, substitutions.map((v, e) => v.underlying -> e.underlying))
      assert(K.isSame(front.underlying, kernel))

  test("capture distinguishes sorts and identifier indices"):
    val otherX = variable[Ind](K.Identifier("capture-x", 1))
    val propX = variable[Prop](x.id)
    val propY = variable[Prop](y.id)
    assert(forall(x, p(y)).substitute(y := otherX).freeVars.contains(otherX))
    val original = forall(x, propY)
    val replaced = original.substitute(propY := propX)
    assert(replaced.freeVars.contains(propX))
    assert(replaced == forall(x, propX))

  test("capture preserves free higher-order variables"):
    val q = variable[Ind >>: Prop](K.Identifier("capture-q"))
    val expression = λ(p, q(x))
    val replaced = expression.substitute(q := p)
    assert(replaced.freeVars.contains(p))
    assert(!replaced.freeVars.contains(q))
