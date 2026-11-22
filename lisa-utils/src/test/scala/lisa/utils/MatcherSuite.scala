package lisa.utils

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.unification.UnificationUtils._
import org.scalatest.funsuite.AnyFunSuite

class MatcherSuite extends AnyFunSuite:
  private given RewriteContext = RewriteContext.empty
  private val x, y, a = variable[Ind]
  private val p, q, r = variable[Prop]
  private val f = Constant[Ind >>: Ind >>: Ind]("matcher-f")

  test("repeated variables respect identity constraints in either traversal order"):
    assert(matchExpr(f(x)(x), f(x)(a)).isEmpty)
    assert(matchExpr(f(x)(x), f(a)(x)).isEmpty)
    val matched = matchExpr(f(x)(x), f(a)(a)).get
    assert(matched(x).contains(a))
    assert(isSame(f(x)(x).substitute(matched.asSubstPair*), f(a)(a)))

  test("identity matches constrain subsequent matching without changing the input substitution"):
    val initial = Substitution.empty
    val matched = matchExpr(x, x, initial).get
    assert(matched(x).contains(x))
    assert(!initial.contains(x))
    assert(matchExpr(x, a, matched).isEmpty)
    val assigned = initial + (x -> a)
    assert(matchExpr(x, x, assigned).isEmpty)
    assert(matchExpr(f(x)(x), f(x)(x), assigned).isEmpty)

  test("retain equivalence matching for structurally different formulas"):
    val source = p /\ q
    val target = q /\ p
    val matched = matchExpr(source, target).get
    assert(matched(p).contains(p))
    assert(matched(q).contains(q))
    assert(isSame(source.substitute(matched.asSubstPair*), target))
    assert(matchExpr(p, r, matched).isEmpty)

  test("variables occurring only in the reference remain unconstrained by the shortcut"):
    val source = p /\ (q \/ !q)
    val matched = matchExpr(source, p).get
    assert(matched(p).contains(p))
    assert(!matched.contains(q))
    val extended = matchExpr(q, r, matched).get
    assert(isSame(source.substitute(extended.asSubstPair*), p))
    val existing = matchExpr(source, p, Substitution.empty + (q -> r)).get
    assert(existing(q).contains(r))
    assert(isSame(source.substitute(existing.asSubstPair*), p))

  test("a conflicting shortcut still permits successful structural matching"):
    val initial = Substitution.empty + (p -> q) + (q -> p)
    val matched = matchExpr(p /\ q, q /\ p, initial).get
    assert(matched(p).contains(q))
    assert(matched(q).contains(p))
    assert(isSame((p /\ q).substitute(matched.asSubstPair*), q /\ p))

  test("rigid variables and constants match without acquiring assignments"):
    val rigid = RewriteContext.withBound(List(x))
    val matched = matchExpr(using rigid)(x, x).get
    assert(!matched.contains(x))
    assert(matchExpr(using rigid)(x, a).isEmpty)
    assert(matchExpr(f, f).nonEmpty)
    assert(matchExpr(f, Constant[Ind >>: Ind >>: Ind]("matcher-g")).isEmpty)

  test("preserve existing identity-equivalent assignments"):
    val replacement = λ(y, y)(x)
    val matched = matchExpr(x, x, Substitution.empty + (x -> replacement)).get
    assert(matched(x).contains(replacement))

  test("the shortcut constrains free higher-sort parameters but leaves bound variables rigid"):
    val h = variable[Ind >>: Ind]
    val matched = matchExpr(λ(x, h(x)), λ(y, h(y))).get
    assert(matched(h).contains(h))
    assert(!matched.contains(x) && !matched.contains(y))
    assert(matchExpr(λ(x, a), λ(y, y)).isEmpty)

  test("binder freshening avoids existing substitution keys and variables nested in values"):
    val z, w = variable[Ind]
    val source = λ(x, z)
    val target = λ(y, a)
    val collision = x.freshRename(Seq(z, a))
    val substitutions = List(
      Substitution.empty + (collision -> a),
      Substitution.empty + (w -> f(collision)(a))
    )
    for initial <- substitutions do
      val matched = matchExpr(source, target, initial).get
      assert(matched(z).contains(a))
      assert(initial.asSubstPair.forall(pair => matched(pair._1).contains(pair._2)))
      assert(!initial.contains(z))
      assert(isSame(source.substitute(matched.asSubstPair*), target))

  test("avoiding existing assignments still rejects escapes from nested binders"):
    val z, w = variable[Ind]
    val source = λ(x, λ(y, f(x)(z)))
    val target = λ(a, λ(w, f(a)(a)))
    val initial = Substitution.empty + (w -> x.freshRename(Seq(z, a)))
    assert(matchExpr(source, target, initial).isEmpty)
