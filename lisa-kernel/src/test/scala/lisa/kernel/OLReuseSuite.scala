package lisa.kernel

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class OLReuseSuite extends AnyFunSuite:
  private val x = Variable(Identifier("reuse-x"), Ind)
  private val y = Variable(Identifier("reuse-y"), Ind)
  private val sx = SimpleVariable(x.id, Ind, true)
  private val sy = SimpleVariable(y.id, Ind, true)
  private val f = SimpleConstant(Identifier("reuse-f"), Ind -> Ind, true)

  // Keep the original scope conversion as a differential oracle.
  private def original(e: SimpleExpression, env: Map[(Identifier, Sort), Int], depth: Int): SimpleExpression = e match
    case SimpleAnd(cs, p) => SimpleAnd(cs.map(original(_, env, depth)), p)
    case SimpleForall(v, b, p) => SimpleForall(v, original(b, env + ((v, Ind) -> depth), depth + 1), p)
    case SimpleEquality(l, r, p) => SimpleEquality(original(l, env, depth), original(r, env, depth), p)
    case v: SimpleVariable => env.get((v.id, v.sort)).fold[SimpleExpression](v)(d => SimpleBoundVariable(depth - d, v.sort, v.polarity))
    case v: SimpleBoundVariable => throw new IllegalArgumentException("Unexpected bound input")
    case SimpleApplication(f, a, p) => SimpleApplication(original(f, env, depth), original(a, env, depth), p)
    case SimpleLambda(v, b) => SimpleLambda(v, original(b, env + ((v.id, v.sort) -> depth), depth + 1))
    case _ => e

  test("retain unchanged applications and vacuous abstractions through conversion and normalization"):
    val app = SimpleApplication(f, sy, true)
    val lam = SimpleLambda(x, app)
    assert(toLocallyNameless(app) eq app)
    assert(toLocallyNameless(lam) eq lam)
    assert(toLocallyNameless2(app, Map((x.id, Ind) -> 0), 1) eq app)
    assert(fromLocallyNameless(lam, Map.empty, 0) eq lam)
    assert(computeNormalForm(app) eq app)
    assert(computeNormalForm(lam) eq lam)

  test("rebuild changed paths while retaining unchanged siblings"):
    val app = SimpleApplication(f, sx, true)
    val converted = toLocallyNameless(SimpleLambda(x, app)).asInstanceOf[SimpleLambda]
    val body = converted.body.asInstanceOf[SimpleApplication]
    assert(!(body eq app))
    assert(body.f eq f)
    assert(body.arg == SimpleBoundVariable(1, Ind, true))
    assert(fromLocallyNameless(converted, Map.empty, 0) == SimpleLambda(x, app))

  test("isolate sibling scopes, nested depths, shadowing and same-named different sorts"):
    val px = SimpleVariable(x.id, Prop, false)
    val shared = SimpleEquality(sx, sy, true)
    val inputs = Seq(
      SimpleAnd(Seq(SimpleForall(x.id, shared, true), SimpleForall(y.id, shared, false)), true),
      SimpleForall(x.id, SimpleAnd(Seq(shared, SimpleForall(y.id, shared, true)), true), true),
      SimpleForall(x.id, SimpleForall(x.id, shared, true), true),
      SimpleLambda(Variable(x.id, Prop), SimpleAnd(Seq(px, shared), true))
    )
    inputs.foreach: e =>
      val converted = toLocallyNameless2(e, Map.empty, 0)
      assert(converted == original(e, Map.empty, 0))
      assert(fromLocallyNameless(converted, Map.empty, 0) == e)

  test("agree with original conversion for shared generated terms and changing environments"):
    val g = SimpleConstant(Identifier("reuse-g"), Ind -> (Ind -> Ind), true)
    val terms = Iterator.iterate[SimpleExpression](sx)(t => SimpleApplication(SimpleApplication(g, t, true), t, true)).take(8).toVector
    val envs = Seq(Map.empty[(Identifier, Sort), Int], Map((x.id, Ind) -> 0), Map((x.id, Prop) -> 0), Map((x.id, Ind) -> 2))
    for term <- terms; env <- envs do
      val e = SimpleAnd(Seq(SimpleEquality(term, sy, false), SimpleForall(x.id, SimpleEquality(term, sx, true), false)), true)
      assert(toLocallyNameless2(e, env, 3) == original(e, env, 3))

  test("still normalize formulas embedded inside term applications and abstractions"):
    val p = SimpleVariable(Identifier("reuse-p"), Prop, true)
    val contradiction = SimpleAnd(Seq(p, getInversePolar(p)), true)
    val h = SimpleConstant(Identifier("reuse-h"), Prop -> Ind, true)
    val app = SimpleApplication(h, contradiction, true)
    val lam = SimpleLambda(x, app)
    val result = computeNormalForm(lam).asInstanceOf[SimpleLambda]
    assert(!(result eq lam))
    assert(result.body == SimpleApplication(h, SimpleLiteral(false), true))
    assert(computeNormalForm(getInversePolar(p)) == getInversePolar(p))

  test("keep rejection of unexpected and unbound de Bruijn nodes"):
    val bound = SimpleBoundVariable(1, Ind, true)
    intercept[Exception](toLocallyNameless(bound))
    intercept[Exception](toLocallyNameless2(SimpleApplication(f, bound, true), Map.empty, 0))
    intercept[Exception](fromLocallyNameless(bound, Map.empty, 0))
