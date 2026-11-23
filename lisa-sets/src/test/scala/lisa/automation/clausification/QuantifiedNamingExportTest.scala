package lisa.automation.clausification

import lisa.automation.ProofSyntax.{_, given}
import lisa.automation.clausification.Clausification.Counter
import lisa.automation.superposition.Sctptp
import lisa.automation.superposition.SctptpTest
import lisa.kernel.KernelProof
import org.scalatest.funsuite.AnyFunSuite
import sctptp.LVL2.LVL2Proof
import sctptp.LVL2.RightSubstIffForall
import sctptp.{SequentCalculus => SC}

class QuantifiedNamingExportTest extends AnyFunSuite:
  private val x = Variable(Identifier("x"), Ind)
  private val y = Variable(Identifier("y"), Ind)
  private val p = Constant(Identifier("p"), Ind -> Prop)
  private val q = Constant(Identifier("q"), Ind -> Prop)
  private val hole = Variable(Identifier("h"), Ind -> Prop)

  test("naming beneath two binders uses the imported definition in a single rightSubstIffForall") {
    val source = exists(x, forall(y, or(and(p(x))(q(y)))(and(p(y))(q(x)))))
    val naming = NamingPhase.nameOne(source, Counter(), 2, Counter(), Set.empty).get
    assert(naming.freeVars.toSet == Set(x, y))
    KernelProof.assertCorrectProofNoSorry(naming.bridge, "quantified naming bridge")
    val proof = SctptpTest.checked(naming.bridge)
    assert(proof.isInstanceOf[LVL2Proof])
    assert(proof.steps.size == 3)
    val rewrite = proof.steps.last.asInstanceOf[RightSubstIffForall]
    assert(rewrite.source == proof.steps(1).name && rewrite.comparison == proof.steps.head.name)
    assert(proof.steps(1).isInstanceOf[SC.Hyp])
  }

  test("an open comparison is universally closed before rewriting with it") {
    val before = exists(y, p(y))
    val after = exists(y, q(y))
    val extra = Constant(Identifier("r"), Prop)
    val premise = () |- before
    val comparison = extra |- (extra, iff(p(x))(q(x)))
    val step = RightSubst(extra |- (extra, after), -1, Seq(-2), Seq((p, q, Seq(x))), (Seq(hole), exists(y, hole(y))))
    val cert = ProofCertificate(Vector(step), Vector(premise, comparison))
    KernelProof.assertCorrectProofNoSorry(cert, "open comparison")
    val proof = SctptpTest.checked(cert)
    assert(proof.steps.count(_.isInstanceOf[SC.RightForall]) == 1)
    assert(proof.steps.last.isInstanceOf[RightSubstIffForall])
    assert(Sctptp.fromKernel(cert.copy(imports = Vector(premise, p(x) |- iff(p(x))(q(x))))).isLeft)
  }

  test("a shared local rewrite remains available after a cut uses the definition directly") {
    val definition = forall(x, iff(p(x))(q(x)))
    val before = exists(y, p(y))
    val after = exists(y, q(y))
    val local = RightSubstEq(definition |- after, -1, Seq(p -> q), (Seq(hole), exists(y, hole(y))))
    val cut = Cut(() |- after, -2, 0, definition)
    val reuse = RightAnd(definition |- and(after)(after), Seq(0, 1), Seq(after, after))
    val proof = SctptpTest.checked(ProofCertificate(Vector(local, cut, reuse), Vector(() |- before, () |- definition)))
    assert(proof.steps.count(_.isInstanceOf[RightSubstIffForall]) == 2)
    assert(proof.steps.count(_.isInstanceOf[SC.Hyp]) == 1)
  }

  test("a certified superposition refutation with quantified naming round-trips") {
    import Clausification.{ClausifierOptions, Distribute, Nnf}
    import lisa.automation.Problem
    import lisa.automation.superposition.Prover

    val f = exists(x, or(and(p(x))(q(x)))(and(q(x))(p(x))))
    val problem = Problem(Vector(() |- f, () |- forall(y, neg(p(y)))), None)
    val options = ClausifierOptions(threshold = 2, distribute = Distribute.Primitive, nnf = Nnf.Primitive)
    val certificate = Prover.proveKernel(problem, clausifierOptions = options).fold(outcome => fail(outcome.toString), identity)
    KernelProof.assertCorrectProofNoSorry(certificate, "refuting quantified naming")
    val linear = certificate.toLinearProof
    val redundant = linear.steps.zipWithIndex.collect { case (Restate(goal, ref), i) if goal == (if ref < 0 then linear.imports(-ref - 1) else linear.steps(ref).statement) => i }
    assert(redundant.isEmpty, s"Restatements of identical imports at steps ${redundant.mkString(", ")}")
    val proof = SctptpTest.checked(certificate)
    assert(proof.conclusion == SC.Sequent(Nil, Nil))
    assert(proof.steps.exists(_.isInstanceOf[RightSubstIffForall]))
  }
