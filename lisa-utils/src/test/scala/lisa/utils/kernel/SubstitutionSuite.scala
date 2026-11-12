package lisa.utils.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.{proof => K}
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionSuite extends AnyFunSuite:
  private given K.Theory = K.Theory.empty
  private val x = Variable(Identifier("x"), Ind)
  private val y = Variable(Identifier("y"), Ind)
  private val z = Variable(Identifier("z"), Ind)
  private val p = Constant(Identifier("P"), Ind -> (Ind -> Prop))
  private val f = Constant(Identifier("f"), Ind -> Ind)
  private val g = Constant(Identifier("g"), Ind -> Ind)
  private val h = Variable(Identifier("h"), Ind -> Ind)

  private def proof(formula: Expression): K.Thm = K.Axiom(K.Sequent(Set.empty, Set(formula))).toOption.get

  private def simultaneous(pairs: Seq[(Expression, Expression)], holes: Seq[Variable], body: Expression, onLeft: Boolean = false): Unit =
    val before = substituteVariables(body, holes.zip(pairs.map(_._1)).toMap)
    val after = substituteVariables(body, holes.zip(pairs.map(_._2)).toMap)
    val equations = Substitution.liftedEqualities(pairs).toSet
    val premise = if onLeft then K.Axiom(K.Sequent(Set(before), Set.empty)).toOption.get else proof(before)
    val target = if onLeft then K.Sequent(equations + after, Set.empty) else K.Sequent(equations, Set(after))
    val result = Substitution.simultaneous(target, premise, pairs, holes -> body, onLeft)
    assert(result.isRight, result.toString)
    assert(result.toOption.get.axioms == premise.axioms)

  test("preserve simultaneous swaps and overlapping replacement terms on both sides"):
    for onLeft <- Seq(false, true) do
      simultaneous(Seq(x -> y, y -> x), Seq(x, y), p(x)(y), onLeft)
      simultaneous(Seq(x -> f(y), y -> g(x)), Seq(x, y), p(x)(y), onLeft)

  test("preserve last-write-wins parameters and require all supplied comparisons"):
    simultaneous(Seq(x -> y, y -> z), Seq(x, x), p(x)(x))
    val target = K.Sequent(Set(equality(y)(z)), Set(p(z)(z)))
    assert(Substitution.simultaneous(target, proof(p(y)(y)), Seq(x -> y, y -> z), Seq(x, x) -> p(x)(x), false).isLeft)

  test("avoid capture beneath binders"):
    simultaneous(Seq(x -> y), Seq(x), forall(Lambda(y, p(x)(y))))

  test("instantiate universally quantified function and predicate comparisons"):
    simultaneous(Seq(f -> g), Seq(h), p(h(x))(y))
    val a = Constant(Identifier("a"), Ind -> Prop)
    val b = Constant(Identifier("b"), Ind -> Prop)
    val v = Variable(Identifier("v"), Ind -> Prop)
    simultaneous(Seq(a -> b), Seq(v), forall(Lambda(x, v(x))))

  test("use a lifted proof without retaining its equality as an assumption"):
    val comparison = proof(Substitution.liftedEqualities(Seq(f -> g)).head)
    val premise = proof(p(f(x))(y))
    val target = K.Sequent(Set.empty, Set(p(g(x))(y)))
    val result = Substitution.withProof(target, premise, comparison, f -> g, h -> p(h(x))(y), false)
    assert(result.isRight, result.toString)
    assert(result.toOption.get.axioms == premise.axioms ++ comparison.axioms)

  test("instantiate binary comparisons in argument order on both sides"):
    val sort = Ind -> (Ind -> Ind)
    val source = Constant(Identifier("binary-f"), sort)
    val target = Constant(Identifier("binary-g"), sort)
    val hole = Variable(Identifier("binary-hole"), sort)
    for onLeft <- Seq(false, true) do
      simultaneous(Seq(source -> target), Seq(hole), p(hole(x)(y))(z), onLeft)
      val comparison = proof(Substitution.liftedEqualities(Seq(source -> target)).head)
      val before = p(source(x)(y))(z)
      val after = p(target(x)(y))(z)
      val premise = K.Axiom(if onLeft then K.Sequent(Set(before), Set.empty) else K.Sequent(Set.empty, Set(before))).toOption.get
      val statement = if onLeft then K.Sequent(Set(after), Set.empty) else K.Sequent(Set.empty, Set(after))
      val result = Substitution.withProof(statement, premise, comparison, source -> target, hole -> p(hole(x)(y))(z), onLeft)
      assert(result.isRight, result.toString)
      assert(result.toOption.get.axioms == premise.axioms ++ comparison.axioms)

  test("retain an OL-equivalent quantified assumption with extra syntactic free variables"):
    val equation = Substitution.liftedEqualities(Seq(f -> g)).head
    val collision = Variable(Identifier("x", 1), Ind)
    val assumption = or(equation)(and(p(collision)(collision))(bot))
    val premise = proof(p(f(x))(y))
    val statement = K.Sequent(Set(assumption), Set(p(g(x))(y)))
    val result = Substitution.simultaneous(statement, premise, Seq(f -> g), Seq(h) -> p(h(x))(y), false)
    assert(result.isRight, result.toString)
    assert(result.toOption.get.left == Set(assumption))
    assert(result.toOption.get.axioms == premise.axioms)

  test("proved ground comparisons retain their residual contexts and reject unrelated proofs"):
    val extra = Constant(Identifier("comparison-extra"), Prop)
    val premise = proof(p(x)(x))
    val comparison = K.Axiom(K.Sequent(Set(extra), Set(equality(x)(y), extra))).toOption.get
    val statement = K.Sequent(Set(extra), Set(p(y)(y), extra))
    val result = Substitution.withProof(statement, premise, comparison, x -> y, x -> p(x)(x), false)
    assert(result.isRight, result.toString)
    assert(result.toOption.get.axioms == premise.axioms ++ comparison.axioms)
    assert(Substitution.withProof(statement, premise, proof(equality(x)(z)), x -> y, x -> p(x)(x), false).isLeft)

  test("reject dropped contexts and malformed replacement sorts"):
    val alpha = Constant(Identifier("alpha"), Prop)
    val premise = K.Axiom(K.Sequent(Set(alpha), Set(p(x)(x)))).toOption.get
    val target = K.Sequent(Set(equality(x)(y)), Set(p(y)(y)))
    assert(Substitution.simultaneous(target, premise, Seq(x -> y), Seq(x) -> p(x)(x), false).isLeft)
    assert(Substitution.simultaneous(target, premise, Seq(x -> alpha), Seq(x) -> p(x)(x), false).isLeft)
    assert(Substitution.simultaneous(target, premise, Seq(x -> y), Seq.empty -> p(x)(x), false).isLeft)

  test("an empty replacement is checked weakening"):
    simultaneous(Seq.empty, Seq.empty, p(x)(y))
    assert(Substitution.simultaneous(K.Sequent(Set.empty, Set(p(y)(x))), proof(p(x)(y)), Nil, Nil -> p(x)(y), false).isLeft)

  test("linear primitive checks both premise indices and retains import dependencies"):
    val premise = K.Sequent(Set.empty, Set(p(x)(x)))
    val comparison = K.Sequent(Set.empty, Set(equality(x)(y)))
    val target = K.Sequent(Set.empty, Set(p(y)(y)))
    val step = RightSubst(target, -1, Seq(-2), Seq((x, y, Nil)), Seq(x) -> p(x)(x))
    val certificate = LinearProof(Array(step), Array(premise, comparison))
    assert(certificate.check.toOption.get.assumptions == Set(premise, comparison))
    assert(certificate.copy(steps = Array(step.copy(comparisons = Seq(0)))).check == Left(ForwardReferenceError(0)))
    assert(ProofStep.mapPremises(step, _ - 2).premises.sameElements(Array(-3, -4)))

  test("linear simultaneous substitution checks every comparison reference"):
    val premise = K.Sequent(Set.empty, Set(p(x)(y)))
    val comparisons = Array(K.Sequent(Set.empty, Set(equality(x)(y))), K.Sequent(Set.empty, Set(equality(y)(x))))
    val target = K.Sequent(Set.empty, Set(p(y)(x)))
    val step = RightSubst(target, -1, Seq(-2, -3), Seq((x, y, Nil), (y, x, Nil)), Seq(x, y) -> p(x)(y))
    val imports = Array(premise) ++ comparisons
    val certificate = LinearProof(Array(step), imports)
    assert(certificate.check.toOption.get.assumptions == imports.toSet)
    assert(certificate.copy(steps = Array(step.copy(comparisons = Seq(-2, 0)))).check == Left(ForwardReferenceError(0)))
    assert(certificate.copy(steps = Array(step.copy(comparisons = Seq(-2, -4)))).check.isLeft)
    assert(ProofStep.mapPremises(step, _ - 3).premises.sameElements(Array(-4, -5, -6)))
