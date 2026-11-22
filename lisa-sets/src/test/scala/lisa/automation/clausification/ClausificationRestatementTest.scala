package lisa.automation.clausification

import lisa.automation.Problem
import lisa.automation.ProofSyntax.{_, given}
import lisa.automation.clausification.Clausification.*
import lisa.automation.superposition.SctptpTest
import lisa.kernel.KernelProof
import org.scalatest.funsuite.AnyFunSuite

class ClausificationRestatementTest extends AnyFunSuite:
  private val p = Constant(Identifier("p"), Prop)
  private val pred = Constant(Identifier("pred"), Ind -> Prop)
  private val x = Variable(Identifier("x"), Ind)

  private def checkWithoutRestatements(proof: ProofCertificate): Unit =
    KernelProof.assertCorrectProofNoSorry(proof, "clausification")
    proof.toLinearProof.steps.foreach {
      case s: Restate => fail(s"Unexpected restatement: $s")
      case s: RestateTrue => fail(s"Unexpected truth restatement: $s")
      case _ => ()
    }

  test("naming, Skolemization and prenex rewriting cite their imports directly") {
    val q = Constant(Identifier("q"), Prop)
    val input = or(and(p)(q))(and(q)(p))
    val named = NamingPhase.nameOne(input, Counter(), 2, Counter(), Set.empty).get
    checkWithoutRestatements(named.bridge)
    assert(named.bridge.steps.last == Cut(input |- named.named, -1, 1, named.quantified))

    val existential = exists(x, pred(x))
    val skolem = SkolemPhase.skolemizeOne(existential, Counter()).get
    checkWithoutRestatements(skolem.bridge)
    assert(skolem.bridge.steps.last == Cut(existential |- skolem.skoFormula, -2, skolem.bridge.steps.size - 2, skolem.defEq))

    given ClausifierOptions = ClausifierOptions(prenex = Prenex.Rewrite)
    for source <- Seq(forall(x, pred(x)), and(p)(forall(x, pred(x))), p) do
      val (sub, matrix) = PrenexPhase.provePrenex(() |- source, -1, Counter(), nonLibSize = 1)
      assert(sub.proof.conclusion == matrix)
      checkWithoutRestatements(sub.proof)
  }

  test("a clausified conjecture with a cut refutation round-trips through SC-TPTP") {
    val problem = Problem(Seq(() |- p), Some(() |- p))
    val proof = CertifiedClausifier.certifyClausal(problem, clauses => {
      assert(clauses.hypotheses == Seq(() |- p, p |- ()))
      ProofCertificate(Vector(Cut(() |- (), -1, -2, p)), clauses.imports)
    }, ClausifierOptions(nnf = Nnf.Primitive, distribute = Distribute.Primitive))
    assert(proof.conclusion == problem.conjecture.get)
    checkWithoutRestatements(proof)
    SctptpTest.checked(proof)
  }

  // Prove the conjecture from the identical second hypothesis. The first hypothesis is already screened.
  private def screen(second: Expression): ProofCertificate =
    given ClausifierOptions = ClausifierOptions()
    val goal = () |- second
    val problem = Problem(Seq(() |- p, goal), Some(goal))
    val phase = ScreenPhase.certifyScreen(problem, (screened, _) => {
      assert(screened.conjecture.contains(screened.hypotheses(1)))
      ClausificationProof(Vector(Weakening(screened.hypotheses(1), -2)), screened.imports ++ libImports)
    })
    val proof = clausificationProofToProofCertificate(phase)
    assert(proof.conclusion == goal)
    KernelProof.assertCorrectProofNoSorry(proof, "screening")
    proof

  test("screening an already expanded quantifier uses no restatement, including when a free variable is renamed") {
    val y = Variable(Identifier("y"), Ind)
    for source <- Seq(forall(x, pred(x)), forall(x, and(pred(x))(pred(y)))) do
      val proof = screen(source)
      checkWithoutRestatements(proof)
      SctptpTest.checked(proof)
  }

  test("screening restates exactly the changed hypothesis and conjecture, independently of renaming") {
    val schematic = Variable(Identifier("rel"), Ind -> Prop)
    for symbol <- Seq(pred, schematic) do
      val proof = screen(forall(symbol)).toLinearProof
      val restatements = proof.steps.collect { case Restate(target, premise) =>
        val source = if premise < 0 then proof.imports(-premise - 1) else proof.steps(premise).statement
        (source, target)
      }.toList
      val renamed = if symbol == pred then pred else Variable(Identifier(GeneratedNames.inputPred, 1), Ind -> Prop)
      val reduced = () |- forall(renamed)
      val expanded = () |- etaExpandQuantifiers(forall(renamed))
      assert(reduced != expanded)
      assert(restatements == List(reduced -> expanded, expanded -> reduced))
      assert(proof.steps.count(_.isInstanceOf[InstSchema]) == (if symbol == pred then 0 else 2))
  }
