package lisa.utils.prooflib

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.{SCProof, SCProofChecker, Substitution}
import lisa.kernel.proof.SequentCalculus.*
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionSuite extends AnyFunSuite:
  private val x = Variable(Identifier("x"), Ind)
  private val y = Variable(Identifier("y"), Ind)
  private val z = Variable(Identifier("z"), Ind)
  private val p = Constant(Identifier("P"), Ind -> Prop)
  private val q = Constant(Identifier("Q"), Ind -> (Ind -> Prop))
  private val alpha = Constant(Identifier("alpha"), Prop)
  private val beta = Constant(Identifier("beta"), Prop)
  private val gamma = Constant(Identifier("gamma"), Prop)

  private def valid(step: SCProofStep, imports: Sequent*): Boolean =
    SCProofChecker.checkSCProof(SCProof(Vector(step), imports.toVector)).isValid

  private def right(statement: Sequent, premise: Int, comparison: Int, replacement: (Expression, Expression),
      context: (Variable, Expression), arguments: Seq[Variable] = Nil): RightSubst =
    RightSubst(statement, premise, Seq(comparison), Seq((replacement._1, replacement._2, arguments)), Seq(context._1) -> context._2)

  private def left(statement: Sequent, premise: Int, comparison: Int, replacement: (Expression, Expression),
      context: (Variable, Expression), arguments: Seq[Variable] = Nil): LeftSubst =
    LeftSubst(statement, premise, Seq(comparison), Seq((replacement._1, replacement._2, arguments)), Seq(context._1) -> context._2)

  test("transport both ways, retaining all residual contexts"):
    val comparison = Sequent(Set(alpha), Set(equality(x)(y), beta))
    assert(valid(right(Sequent(Set(alpha, gamma), Set(p(y), beta)), -1, -2, x -> y, x -> p(x)),
      Sequent(Set(gamma), Set(p(x))), comparison))
    assert(valid(left(Sequent(Set(alpha, gamma, p(y)), Set(beta)), -1, -2, x -> y, x -> p(x)),
      Sequent(Set(gamma, p(x)), Set.empty), comparison))
    for target <- Seq(Sequent(Set(gamma), Set(p(y), beta)), Sequent(Set(alpha, gamma), Set(p(y))), Sequent(Set(alpha), Set(p(y), beta))) do
      assert(!valid(right(target, -1, -2, x -> y, x -> p(x)), Sequent(Set(gamma), Set(p(x))), comparison))

  test("use equivalence for propositions"):
    val hole = Variable(Identifier("prop"), Prop)
    assert(valid(right(Sequent(Set.empty, Set(beta)), -1, -2, alpha -> beta, hole -> hole),
      Sequent(Set.empty, Set(alpha)), Sequent(Set.empty, Set(iff(alpha)(beta)))))

  test("allow comparison arguments in the main premise, but not residual comparison contexts"):
    val f = Constant(Identifier("f"), Ind -> Prop)
    val g = Constant(Identifier("g"), Ind -> Prop)
    val v = Variable(Identifier("v"), Ind -> Prop)
    val body = and(v(x))(p(x))
    val target = Sequent(Set(p(x)), Set(and(g(x))(p(x))))
    val step = right(target, -1, -2, f -> g, v -> body, Seq(x))
    val premise = Sequent(Set(p(x)), Set(and(f(x))(p(x))))
    val equation = iff(f(x))(g(x))
    assert(valid(step, premise, Sequent(Set.empty, Set(equation))))
    assert(!valid(step, premise, Sequent(Set(p(x)), Set(equation))))
    assert(!valid(step, premise, Sequent(Set.empty, Set(equation, p(x)))))
    assert(!valid(step.copy(replacements = Seq((f, g, Nil))), premise, Sequent(Set.empty, Set(equation))))
    assert(!valid(step.copy(replacements = Seq((Lambda(z, p(x)), g, Seq(x)))), premise, Sequent(Set.empty, Set(equation))))

  test("reject wrong sorts, wrong comparisons and invalid references"):
    val statement = Sequent(Set.empty, Set(p(y)))
    val premise = Sequent(Set.empty, Set(p(x)))
    val comparison = Sequent(Set.empty, Set(equality(x)(y)))
    val step = right(statement, -1, -2, x -> y, x -> p(x))
    assert(!valid(step.copy(replacements = Seq((x, alpha, Nil))), premise, comparison))
    assert(!valid(step, premise, Sequent(Set.empty, Set(equality(x)(z)))))
    assert(!valid(step.copy(comparisons = Seq(0)), premise, comparison))
    assert(!valid(step.copy(comparisons = Seq(-3)), premise, comparison))

  test("support higher-order arguments and reject repeated arguments"):
    val sort = (Ind -> Prop) -> Ind
    val f = Constant(Identifier("higher-f"), sort)
    val g = Constant(Identifier("higher-g"), sort)
    val hole = Variable(Identifier("higher-hole"), sort)
    val argument = Variable(Identifier("higher-argument"), Ind -> Prop)
    val observer = Constant(Identifier("observer"), sort -> Prop)
    assert(valid(right(Sequent(Set.empty, Set(observer(g))), -1, -2, f -> g, hole -> observer(hole), Seq(argument)),
      Sequent(Set.empty, Set(observer(f))), Sequent(Set.empty, Set(equality(f(argument))(g(argument))))))
    val binary = Ind -> (Ind -> Ind)
    val ff = Constant(Identifier("binary-f"), binary)
    val gg = Constant(Identifier("binary-g"), binary)
    val v = Variable(Identifier("binary-hole"), binary)
    val observe = Constant(Identifier("binary-observer"), binary -> Prop)
    assert(!valid(right(Sequent(Set.empty, Set(observe(gg))), -1, -2, ff -> gg, v -> observe(v), Seq(x, x)),
      Sequent(Set.empty, Set(observe(ff))), Sequent(Set.empty, Set(equality(ff(x)(x))(gg(x)(x))))))

  test("derive simultaneous swaps, overlaps and duplicate parameters on both sides"):
    for onLeft <- Seq(false, true); (pairs, holes) <- Seq(
      Seq(x -> y, y -> x) -> Seq(x, y), Seq(x -> y, y -> z) -> Seq(x, x)
    ) do
      val body = q(x)(y)
      val before = substituteVariables(body, holes.zip(pairs.map(_._1)).toMap)
      val after = substituteVariables(body, holes.zip(pairs.map(_._2)).toMap)
      val equations = Substitution.liftedEqualities(pairs).toSet
      val premise = if onLeft then Sequent(Set(before), Set.empty) else Sequent(Set.empty, Set(before))
      val target = if onLeft then Sequent(equations + after, Set.empty) else Sequent(equations, Set(after))
      val certificate = Substitution.simultaneous(target, premise, pairs, holes -> body, onLeft).toOption.get
      assert(SCProofChecker.checkSCProof(certificate).isValid)
      assert(!certificate.steps.exists(step => step.isInstanceOf[LeftSubstEq] || step.isInstanceOf[RightSubstEq]))
      val old = if onLeft then LeftSubstEq(target, -1, pairs, holes -> body) else RightSubstEq(target, -1, pairs, holes -> body)
      assert(valid(old, premise))

  test("derive quantified function substitution and retain OL-equivalent assumptions"):
    val f = Constant(Identifier("f"), Ind -> Ind)
    val g = Constant(Identifier("g"), Ind -> Ind)
    val v = Variable(Identifier("v"), Ind -> Ind)
    val equation = Substitution.liftedEqualities(Seq(f -> g)).head
    val certificate = Substitution.simultaneous(Sequent(Set(equation), Set(p(g(x)))), Sequent(Set.empty, Set(p(f(x)))), Seq(f -> g), Seq(v) -> p(v(x)), false).toOption.get
    assert(SCProofChecker.checkSCProof(certificate).isValid)
    val prop = Variable(Identifier("prop"), Prop)
    assert(valid(RightSubstEq(Sequent(Set(alpha), Set(alpha)), -1, Seq(top -> alpha), Seq(prop) -> prop), Sequent(Set.empty, Set(top))))

  test("substitution avoids capture beneath a binder"):
    val body = forall(Lambda(y, q(x)(y)))
    val target = Sequent(Set(equality(x)(y)), Set(substituteVariables(body, Map(x -> y))))
    assert(valid(RightSubstEq(target, -1, Seq(x -> y), Seq(x) -> body), Sequent(Set.empty, Set(body))))

  test("instantiate binary comparisons in argument order on both sides"):
    val sort = Ind -> (Ind -> Ind)
    val f = Constant(Identifier("binary-f"), sort)
    val g = Constant(Identifier("binary-g"), sort)
    val hole = Variable(Identifier("binary-hole"), sort)
    val equation = Substitution.liftedEqualities(Seq(f -> g)).head
    val before = p(f(x)(y))
    val after = p(g(x)(y))
    for onLeft <- Seq(false, true) do
      val premise = if onLeft then Sequent(Set(before), Set.empty) else Sequent(Set.empty, Set(before))
      val result = if onLeft then Sequent(Set(after), Set.empty) else Sequent(Set.empty, Set(after))
      val assumed = result.copy(left = result.left + equation)
      val pairs = Substitution.simultaneous(assumed, premise, Seq(f -> g), Seq(hole) -> p(hole(x)(y)), onLeft).toOption.get
      assert(SCProofChecker.checkSCProof(pairs).isValid)
      val comparison = Sequent(Set.empty, Set(equation))
      val proved = Substitution.withProof(result, premise, comparison, f -> g, hole -> p(hole(x)(y)), onLeft).toOption.get
      assert(SCProofChecker.checkSCProof(proved).isValid)

  test("retain an OL-equivalent quantified assumption with extra syntactic free variables"):
    val f = Constant(Identifier("f"), Ind -> Ind)
    val g = Constant(Identifier("g"), Ind -> Ind)
    val hole = Variable(Identifier("hole"), Ind -> Ind)
    val equation = Substitution.liftedEqualities(Seq(f -> g)).head
    val collision = Variable(Identifier("x", 1), Ind)
    val assumption = or(equation)(and(p(collision))(bot))
    val premise = Sequent(Set.empty, Set(p(f(x))))
    val statement = Sequent(Set(assumption), Set(p(g(x))))
    val certificate = Substitution.simultaneous(statement, premise, Seq(f -> g), Seq(hole) -> p(hole(x)), false).toOption.get
    assert(SCProofChecker.checkSCProof(certificate).isValid)
    assert(certificate.conclusion == statement)

  test("proved ground comparisons retain their residual contexts and reject unrelated proofs"):
    val premise = Sequent(Set.empty, Set(p(x)))
    val comparison = Sequent(Set(alpha), Set(equality(x)(y), beta))
    val statement = Sequent(Set(alpha), Set(p(y), beta))
    val certificate = Substitution.withProof(statement, premise, comparison, x -> y, x -> p(x), false).toOption.get
    assert(SCProofChecker.checkSCProof(certificate).isValid)
    assert(certificate.imports == Vector(premise, comparison))
    val unrelated = Sequent(Set.empty, Set(equality(x)(z)))
    val rejected = Substitution.withProof(statement, premise, unrelated, x -> y, x -> p(x), false)
    assert(!rejected.exists(SCProofChecker.checkSCProof(_).isValid))

  test("an empty replacement still checks weakening"):
    assert(valid(RightSubstEq(Sequent(Set.empty, Set(p(x))), -1, Nil, Nil -> p(x)), Sequent(Set.empty, Set(p(x)))))
    assert(!valid(RightSubstEq(Sequent(Set.empty, Set(p(y))), -1, Nil, Nil -> p(y)), Sequent(Set.empty, Set(p(x)))))

  test("report a rejected derived rule at its original certificate position"):
    import lisa.kernel.proof.SCProofCheckerJudgement.*
    val premise = Sequent(Set(alpha), Set(p(x)))
    val step = RightSubstEq(Sequent(Set(equality(x)(y)), Set(p(y))), -1, Seq(x -> y), Seq(x) -> p(x))
    val certificate = SCProof(Vector(step), Vector(premise))
    SCProofChecker.checkSCProof(certificate) match
      case SCInvalidProof(proof, path, _) => assert(proof == certificate && path == Seq(0))
      case _ => fail("Expected rejection of a dropped premise context")

  test("serialize both new primitives and remap their two references"):
    import java.io.*
    import lisa.utils.{Serialization, KernelHelpers}
    assert(Serialization.Tag.leftSubst == 33 && Serialization.Tag.rightSubst == 34)
    for onLeft <- Seq(false, true) do
      val target = if onLeft then Sequent(Set(p(y)), Set.empty) else Sequent(Set.empty, Set(p(y)))
      val premise = if onLeft then Sequent(Set(p(x)), Set.empty) else Sequent(Set.empty, Set(p(x)))
      val comparison = Sequent(Set.empty, Set(equality(x)(y)))
      val step = if onLeft then left(target, -1, -2, x -> y, x -> p(x)) else right(target, -1, -2, x -> y, x -> p(x))
      val certificate = SCProof(Vector(step), Vector(premise, comparison))
      val trees = ByteArrayOutputStream()
      val steps = ByteArrayOutputStream()
      Serialization.proofsToDataStream(DataOutputStream(trees), DataOutputStream(steps), Seq(("subst", certificate, Nil)))
      val restored = Serialization.proofsFromDataStream(DataInputStream(ByteArrayInputStream(trees.toByteArray)), DataInputStream(ByteArrayInputStream(steps.toByteArray))).head._2
      assert(restored == certificate)
      assert(SCProofChecker.checkSCProof(restored).isValid)
      assert(KernelHelpers.mapStepPremises(step, _ - 2).premises == Seq(-3, -4))

  test("perform mixed simultaneous replacements with separate comparison contexts"):
    val f = Constant(Identifier("mixed-f"), Ind -> Prop)
    val g = Constant(Identifier("mixed-g"), Ind -> Prop)
    val v = Variable(Identifier("mixed-hole"), Ind -> Prop)
    val argument = Variable(Identifier("mixed-argument"), Ind)
    val observer = Constant(Identifier("mixed-observer"), (Ind -> Prop) -> Prop)
    val body = and(p(x))(observer(v))
    val premise = Sequent(Set.empty, Set(and(p(y))(observer(f))))
    val first = Sequent(Set(alpha), Set(equality(y)(z), beta))
    val second = Sequent(Set(gamma), Set(iff(f(argument))(g(argument))))
    val target = Sequent(Set(alpha, gamma), Set(and(p(z))(observer(g)), beta))
    val replacements = Seq((y: Expression, z: Expression, Seq.empty[Variable]), (f: Expression, g: Expression, Seq(argument)))
    val step = RightSubst(target, -1, Seq(-2, -3), replacements, Seq(x, v) -> body)
    assert(valid(step, premise, first, second))
    assert(!valid(step.copy(comparisons = Seq(-2)), premise, first, second))
    assert(!valid(step.copy(comparisons = Seq(-2, -3, -2)), premise, first, second))
    assert(!valid(step.copy(context = Seq(x) -> body), premise, first, second))
    assert(!valid(step.copy(context = Seq(x, v, z) -> body), premise, first, second))
    assert(!valid(step.copy(bot = target.copy(left = Set(alpha))), premise, first, second))
    assert(!valid(step.copy(comparisons = Seq(-2, 0)), premise, first, second))
    assert(!valid(step.copy(comparisons = Seq(-2, -4)), premise, first, second))
    assert(lisa.utils.KernelHelpers.mapStepPremises(step, _ - 3).premises == Seq(-4, -5, -6))
    val trees = new java.io.ByteArrayOutputStream()
    val steps = new java.io.ByteArrayOutputStream()
    val certificate = SCProof(Vector(step), Vector(premise, first, second))
    lisa.utils.Serialization.proofsToDataStream(new java.io.DataOutputStream(trees), new java.io.DataOutputStream(steps), Seq(("simultaneous", certificate, Nil)))
    val restored = lisa.utils.Serialization.proofsFromDataStream(
      new java.io.DataInputStream(new java.io.ByteArrayInputStream(trees.toByteArray)),
      new java.io.DataInputStream(new java.io.ByteArrayInputStream(steps.toByteArray))
    ).head._2
    assert(restored == certificate)
    assert(SCProofChecker.checkSCProof(restored).isValid)
