package lisa.kernel.proof

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionSuite extends AnyFunSuite:
  private given Theory = Theory.empty
  private val s = Constant(Identifier("subst-s"), Ind)
  private val t = Constant(Identifier("subst-t"), Ind)
  private val u = Constant(Identifier("subst-u"), Ind)
  private val x = Variable(Identifier("subst-hole"), Ind)
  private val a = Variable(Identifier("subst-arg"), Ind)
  private val p = Constant(Identifier("subst-p"), Ind -> Prop)
  private val q = Constant(Identifier("subst-q"), Ind -> Prop)
  private val h = Constant(Identifier("subst-h"), (Ind -> Prop) -> Prop)
  private val f = Constant(Identifier("subst-f"), Ind -> Prop)
  private val g = Constant(Identifier("subst-g"), Ind -> Prop)
  private val v = Variable(Identifier("subst-predicate"), Ind -> Prop)
  private val alpha = Constant(Identifier("subst-alpha"), Prop)
  private val beta = Constant(Identifier("subst-beta"), Prop)
  private val gamma = Constant(Identifier("subst-gamma"), Prop)
  private val delta = Constant(Identifier("subst-delta"), Prop)
  private def proof(left: Set[Expression], right: Set[Expression]): Thm = Axiom(Sequent(left, right)).toOption.get

  private def right(statement: Sequent, premise: Thm, comparison: Thm, replacement: (Expression, Expression),
      context: (Variable, Expression), arguments: Seq[Variable] = Nil): RightSubst.Result[Thm] =
    RightSubst(statement, premise, Seq(comparison), Seq((replacement._1, replacement._2, arguments)), Seq(context._1) -> context._2)

  private def left(statement: Sequent, premise: Thm, comparison: Thm, replacement: (Expression, Expression),
      context: (Variable, Expression), arguments: Seq[Variable] = Nil): LeftSubst.Result[Thm] =
    LeftSubst(statement, premise, Seq(comparison), Seq((replacement._1, replacement._2, arguments)), Seq(context._1) -> context._2)

  test("transport on the right and retain both premises' contexts and dependencies"):
    val premise = proof(Set(alpha), Set(p(s), beta))
    val comparison = proof(Set(gamma), Set(equality(s)(t), delta))
    val target = Sequent(Set(alpha, gamma), Set(p(t), beta, delta))
    val result = right(target, premise, comparison, s -> t, x -> p(x)).toOption.get
    assert(result.statement == target && result.rule == RightSubst)
    assert(result.axioms == premise.axioms ++ comparison.axioms)
    assert(result.assumptions.isEmpty && !result.usesSorry)

  test("transport on the left with the same comparison direction"):
    val premise = proof(Set(p(s), alpha), Set(beta))
    val comparison = proof(Set(gamma), Set(equality(s)(t), delta))
    val target = Sequent(Set(p(t), alpha, gamma), Set(beta, delta))
    assert(left(target, premise, comparison, s -> t, x -> p(x)).isRight)

  test("reject dropping either comparison context or an untouched primary formula"):
    val premise = proof(Set(alpha), Set(p(s), beta))
    val comparison = proof(Set(gamma), Set(equality(s)(t), delta))
    for target <- Seq(
        Sequent(Set(alpha), Set(p(t), beta, delta)),
        Sequent(Set(alpha, gamma), Set(p(t), beta)),
        Sequent(Set(gamma), Set(p(t), beta, delta)),
        Sequent(Set(alpha, gamma), Set(p(t), delta))
      )
    do assert(right(target, premise, comparison, s -> t, x -> p(x)).isLeft)

  test("require the specified comparison and substituted target"):
    val premise = proof(Set.empty, Set(p(s)))
    val wrong = proof(Set.empty, Set(equality(s)(u)))
    val comparison = proof(Set.empty, Set(equality(s)(t)))
    assert(right(Sequent(Set.empty, Set(p(t))), premise, wrong, s -> t, x -> p(x)).isLeft)
    assert(right(Sequent(Set.empty, Set(q(t))), premise, comparison, s -> t, x -> p(x)).isLeft)

  test("replace propositions using equivalence rather than individual equality"):
    val hole = Variable(Identifier("subst-prop"), Prop)
    val premise = proof(Set.empty, Set(and(alpha)(gamma)))
    val comparison = proof(Set.empty, Set(iff(alpha)(beta)))
    assert(right(Sequent(Set.empty, Set(and(beta)(gamma))), premise, comparison, alpha -> beta, hole -> and(hole)(gamma)).isRight)

  test("pointwise arguments may occur in the primary premise and formula context"):
    val body = and(h(v))(p(a))
    val premise = proof(Set(q(a)), Set(and(h(f))(p(a))))
    val comparison = proof(Set.empty, Set(iff(f(a))(g(a))))
    val target = Sequent(Set(q(a)), Set(and(h(g))(p(a))))
    assert(right(target, premise, comparison, f -> g, v -> body, Seq(a)).isRight)

  test("pointwise arguments must be fresh in both residual comparison contexts"):
    val equation = iff(f(a))(g(a))
    val premise = proof(Set.empty, Set(h(f)))
    for comparison <- Seq(proof(Set(p(a)), Set(equation)), proof(Set.empty, Set(equation, p(a)))) do
      val target = Sequent(comparison.left, (comparison.right - equation) + h(g))
      assert(right(target, premise, comparison, f -> g, v -> h(v), Seq(a)).left.exists(_.isInstanceOf[Substitution.ArgumentNotFresh]))

  test("pointwise arguments must be fresh in the compared expressions"):
    val source = Lambda(x, p(a))
    val comparison = proof(Set.empty, Set(iff(source(a))(g(a))))
    assert(right(Sequent(Set.empty, Set(h(g))), proof(Set.empty, Set(h(source))), comparison, source -> g, v -> h(v), Seq(a)).isLeft)

  test("support higher-order comparison argument sorts"):
    val sort = (Ind -> Prop) -> Ind
    val source = Constant(Identifier("higher-source"), sort)
    val target = Constant(Identifier("higher-target"), sort)
    val hole = Variable(Identifier("higher-hole"), sort)
    val argument = Variable(Identifier("higher-argument"), Ind -> Prop)
    val observer = Constant(Identifier("higher-observer"), sort -> Prop)
    val comparison = proof(Set.empty, Set(equality(source(argument))(target(argument))))
    assert(right(Sequent(Set.empty, Set(observer(target))), proof(Set.empty, Set(observer(source))), comparison,
      source -> target, hole -> observer(hole), Seq(argument)).isRight)

  test("reject mismatched sorts, wrong argument arity and repeated comparison arguments"):
    val premise = proof(Set.empty, Set(p(s)))
    val comparison = proof(Set.empty, Set(equality(s)(t)))
    assert(right(Sequent(Set.empty, Set(p(t))), premise, comparison, s -> alpha, x -> p(x)).isLeft)
    assert(right(Sequent(Set.empty, Set(h(g))), proof(Set.empty, Set(h(f))), comparison, f -> g, v -> h(v)).isLeft)
    val sort = Ind -> (Ind -> Ind)
    val ff = Constant(Identifier("subst-ff"), sort)
    val gg = Constant(Identifier("subst-gg"), sort)
    val vv = Variable(Identifier("subst-vv"), sort)
    val observer = Constant(Identifier("subst-observer"), sort -> Prop)
    val equation = equality(ff(a)(a))(gg(a)(a))
    val result = right(Sequent(Set.empty, Set(observer(gg))), proof(Set.empty, Set(observer(ff))), proof(Set.empty, Set(equation)), ff -> gg, vv -> observer(vv), Seq(a, a))
    assert(result.left.exists(_.isInstanceOf[Substitution.RepeatedArgument]))

  test("retain holes and Sorry, and reject a comparison from another theory"):
    val premise = Sorry(Sequent(Set.empty, Set(p(s)))).toOption.get
    val comparison = Assume(Sequent(Set.empty, Set(equality(s)(t)))).toOption.get
    val target = Sequent(Set.empty, Set(p(t)))
    val result = right(target, premise, comparison, s -> t, x -> p(x)).toOption.get
    assert(result.usesSorry && result.assumptions == comparison.assumptions)
    val foreign = Axiom(using Theory.empty)(comparison.statement).toOption.get
    assert(right(target, premise, foreign, s -> t, x -> p(x)).left.exists(_.isInstanceOf[TheoryMismatch]))

  test("substitute simultaneously with separate term and predicate comparisons"):
    val replacements = Seq((s: Expression, t: Expression, Seq.empty[Variable]), (f: Expression, g: Expression, Seq(a)))
    val body = and(p(x))(h(v))
    val premise = proof(Set(alpha), Set(and(p(s))(h(f)), beta))
    val first = proof(Set(gamma), Set(equality(s)(t), delta))
    val second = Assume(Sequent(Set(alpha), Set(iff(f(a))(g(a)), beta))).toOption.get
    val target = Sequent(Set(alpha, gamma), Set(and(p(t))(h(g)), beta, delta))
    val result = RightSubst(target, premise, Seq(first, second), replacements, Seq(x, v) -> body).toOption.get
    assert(result.axioms == premise.axioms ++ first.axioms)
    assert(result.assumptions == second.assumptions)
    assert(!result.usesSorry)

  test("require exactly one context variable and comparison per replacement"):
    val premise = proof(Set.empty, Set(p(s)))
    val comparison = proof(Set.empty, Set(equality(s)(t)))
    val replacements = Seq((s: Expression, t: Expression, Seq.empty[Variable]))
    val target = Sequent(Set.empty, Set(p(t)))
    for (variables, comparisons) <- Seq(
        (Seq.empty[Variable], Seq(comparison)),
        (Seq(x, a), Seq(comparison)),
        (Seq(x), Seq.empty[Thm]),
        (Seq(x), Seq(comparison, comparison))
      )
    do assert(RightSubst(target, premise, comparisons, replacements, variables -> p(x)).left.exists(_.isInstanceOf[Substitution.ArityMismatch]))

  test("substitute multiple terms on the left and retain every comparison context"):
    val y = Variable(Identifier("left-second-hole"), Ind)
    val body = and(p(x))(q(y))
    val before = and(p(s))(q(t))
    val after = and(p(t))(q(u))
    val premise = proof(Set(before, alpha), Set(beta))
    val first = proof(Set(gamma), Set(equality(s)(t), delta))
    val second = proof(Set(beta), Set(equality(t)(u), alpha))
    val target = Sequent(Set(after, alpha, gamma, beta), Set(beta, delta, alpha))
    val replacements = Seq((s: Expression, t: Expression, Seq.empty[Variable]), (t: Expression, u: Expression, Seq.empty[Variable]))
    assert(LeftSubst(target, premise, Seq(first, second), replacements, Seq(x, y) -> body).isRight)
    assert(LeftSubst(target.copy(right = Set(beta, delta)), premise, Seq(first, second), replacements, Seq(x, y) -> body).isLeft)

  test("an empty simultaneous substitution still checks the primary premise"):
    val premise = proof(Set(alpha), Set(p(s)))
    assert(RightSubst(premise.statement, premise, Nil, Nil, Nil -> p(s)).isRight)
    assert(RightSubst(Sequent(Set.empty, Set(p(s))), premise, Nil, Nil, Nil -> p(s)).isLeft)
    assert(RightSubst(Sequent(Set(alpha), Set(p(t))), premise, Nil, Nil, Nil -> p(s)).isLeft)

  test("simultaneous swaps do not rewrite inserted expressions and avoid capture"):
    val y = Variable(Identifier("subst-second-hole"), Ind)
    val body = and(p(x))(q(y))
    val premise = proof(Set.empty, Set(and(p(y))(q(x))))
    val comparisons = Seq(proof(Set.empty, Set(equality(y)(x))), proof(Set.empty, Set(equality(x)(y))))
    val replacements = Seq((y: Expression, x: Expression, Seq.empty[Variable]), (x: Expression, y: Expression, Seq.empty[Variable]))
    assert(RightSubst(Sequent(Set.empty, Set(and(p(x))(q(y)))), premise, comparisons, replacements, Seq(x, y) -> body).isRight)
    val quantified = forall(Lambda(y, equality(x)(y)))
    val before = forall(Lambda(y, equality(s)(y)))
    val after = substituteVariables(quantified, Map(x -> y))
    assert(RightSubst(Sequent(Set.empty, Set(after)), proof(Set.empty, Set(before)),
      Seq(proof(Set.empty, Set(equality(s)(y)))), Seq((s: Expression, y: Expression, Seq.empty[Variable])), Seq(x) -> quantified).isRight)

  test("check every comparison including its residual context and theory"):
    val body = and(p(x))(h(v))
    val replacements = Seq((s: Expression, t: Expression, Seq.empty[Variable]), (f: Expression, g: Expression, Seq(a)))
    val premise = proof(Set.empty, Set(and(p(s))(h(f))))
    val first = proof(Set.empty, Set(equality(s)(t)))
    val target = Sequent(Set.empty, Set(and(p(t))(h(g))))
    val wrong = proof(Set.empty, Set(iff(f(a))(f(a))))
    val residual = proof(Set.empty, Set(iff(f(a))(g(a)), beta))
    val notFresh = proof(Set(p(a)), Set(iff(f(a))(g(a))))
    for second <- Seq(wrong, residual, notFresh) do
      assert(RightSubst(target, premise, Seq(first, second), replacements, Seq(x, v) -> body).isLeft)
    val foreign = Axiom(using Theory.empty)(Sequent(Set.empty, Set(iff(f(a))(g(a))))).toOption.get
    assert(RightSubst(target, premise, Seq(first, foreign), replacements, Seq(x, v) -> body).left.exists(_.isInstanceOf[TheoryMismatch]))
