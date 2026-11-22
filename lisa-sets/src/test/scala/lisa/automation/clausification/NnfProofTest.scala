package lisa.automation.clausification

import lisa.automation.ProofSyntax.{_, given}
import lisa.automation.Problem
import lisa.automation.clausification.Clausification.{ClausifierOptions, Nnf, libImports}
import lisa.automation.superposition.{Prover, Sctptp, SctptpTest}
import lisa.kernel.KernelProof
import org.scalatest.funsuite.AnyFunSuite
import sctptp.{FOL as F, SequentCalculus as SC}

class NnfProofTest extends AnyFunSuite:
  private val p = Constant(Identifier("p"), Prop)
  private val q = Constant(Identifier("q"), Prop)
  private val r = Constant(Identifier("r"), Prop)

  private def check(source: Expression): ProofCertificate =
    val proof = NnfProof(source)
    assert(proof.imports == Vector(() |- source))
    assert(proof.conclusion == (() |- NnfPhase.toNNF(source, negated = false)))
    proof.toLinearProof.steps.foreach {
      case RestateTrue(s) => assert(s == (() |- top) || s == (bot |- ()))
      case s: Restate => fail(s"Unexpected restatement in primitive NNF: $s")
      case _ => ()
    }
    KernelProof.assertCorrectProofNoSorry(proof, "primitive NNF")
    SctptpTest.checked(proof)
    proof

  test("introduces each propositional connective at both polarities") {
    val formulas = Seq(p, neg(p), and(p)(q), or(p)(q), implies(p)(q), iff(p)(q), iff(implies(p)(q))(neg(r)))
    for f <- formulas do
      check(f)
      check(neg(f))
  }

  test("repeated operands and complementary literals survive set contraction") {
    val compound = implies(p)(q)
    for op <- Seq(and, or, implies, iff); other <- Seq(compound, neg(compound)) do
      val source = op(compound)(other)
      check(source)
      check(neg(source))
  }

  test("quantifier duality preserves shadowed binders and free variables") {
    val x = Variable(Identifier("x"), Ind)
    val y = Variable(Identifier("y"), Ind)
    val pred = Constant(Identifier("p"), Ind -> (Ind -> Prop))
    val body = implies(pred(x)(y))(exists(x, neg(pred(y)(x))))
    for quantified <- Seq(forall(x, body), exists(x, body)) do
      for f <- Seq(quantified, neg(quantified)) do
        val proof = check(f)
        assert(proof.conclusion.right.head.freeVariables == Set(y))
  }

  test("Boolean absorption and negation give the same NNF with checked truth and falsity leaves") {
    for op <- Seq(and, or, implies, iff); c <- Seq(top, bot); other <- Seq(p, top, bot) do
      for f <- Seq(op(c)(other), op(other)(c)).distinct do
        check(f)
        check(neg(f))
    check(neg(top))
    check(neg(bot))
  }

  test("only the two exact Boolean sequents are accepted as RestateTrue") {
    for s <- Seq(() |- top, bot |- ()) do SctptpTest.checked(ProofCertificate(RestateTrue(s)))
    for s <- Seq(p |- top, bot |- p, () |- (p, top), p |- p) do
      assert(Sctptp.fromKernel(ProofCertificate(RestateTrue(s))).isLeft)

    val context = SC.Sequent(Nil, Seq(F.AtomicFormula(F.bot, Nil), F.AtomicFormula(F.top, Nil)))
    for i <- Seq(-1, 0, 1, 2) do
      val step = SC.RightTrue("s", context, i)
      assert((SC.checkProof(SC.LVL1Proof(Vector(step), "truth")) == SC.StepCheckOK) == (i == 1))
  }

  test("the NNF phase reuses identical imports and preserves clause order and goal indices in both modes") {
    val source = Vector(r, implies(p)(q), p, neg(neg(q)))
    val problem = Problem(source.map(f => () |- f), None)
    val normals = source.map(NnfPhase.toNNF(_, negated = false))
    for strategy <- Nnf.values do
      given ClausifierOptions = ClausifierOptions(nnf = strategy)
      val phase = NnfPhase.certifyNnf(problem, (transformed, goals) => {
        assert(goals == Set(1, 3))
        assert(transformed.hypotheses == normals.map(f => () |- f))
        val end = RightAnd(() |- multiand(normals), source.indices.map(problem.hypIndex), normals)
        ClausificationProof(Vector(end), transformed.imports ++ libImports)
      }, Set(1, 3))
      val refs = phase.steps.last.asInstanceOf[ClausificationSubproof].premises
      assert(refs == Vector(-1, 0, -3, 1) ++ Clausification.libRefs(source.size))
      val proof = clausificationProofToProofCertificate(phase)
      KernelProof.assertCorrectProofNoSorry(proof, "NNF phase")
      val restates = proof.toLinearProof.steps.count(_.isInstanceOf[Restate])
      if strategy == Nnf.Primitive then
        assert(restates == 0)
        SctptpTest.checked(proof)
      else assert(restates == 2)
  }

  test("proveKernel passes the requested NNF strategy to certified clausification") {
    val source = implies(p)(q)
    val normal = NnfPhase.toNNF(source, negated = false)
    val problem = Problem(Seq(() |- source, () |- p, () |- neg(q)), None)
    for strategy <- Nnf.values do
      val proof = Prover.proveKernel(problem, clausifierOptions = ClausifierOptions(nnf = strategy)).fold(outcome => fail(outcome.toString), identity)
      KernelProof.assertCorrectProofNoSorry(proof, s"proveKernel with $strategy")
      val linear = proof.toLinearProof
      assert(linear.steps.last.statement == (() |- ()))
      val usedRestatement = linear.steps.exists {
        case Restate(s, i) =>
          val premise = if i < 0 then linear.imports(-i - 1) else linear.steps(i).statement
          premise == (() |- source) && s == (() |- normal)
        case _ => false
      }
      assert(usedRestatement == (strategy == Nnf.Restate))
  }
