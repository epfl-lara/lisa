package lisa.automation.clausification

import lisa.automation.Problem
import lisa.automation.ProofSyntax.{_, given}
import lisa.automation.clausification.Clausification._
import lisa.automation.superposition.Clausal
import lisa.automation.superposition.Prover
import lisa.automation.superposition.SctptpTest
import lisa.kernel.KernelProof
import org.scalatest.funsuite.AnyFunSuite
import sctptp.{SequentCalculus => SC}

class EmptyClauseCertificateTest extends AnyFunSuite:
  private val empty = () |- ()

  test("primitive distribution drops truth and proves the single empty clause for falsity") {
    given ClausifierOptions = ClausifierOptions(distribute = Distribute.Primitive)
    val problem = Problem(Vector(() |- top, () |- bot), None)
    val phase = DistributePhase.certifyDistribute(
      problem,
      (clauses, goal) => {
        assert(clauses.imports == Vector(empty))
        assert(goal == Set(0))
        ClausificationProof(Vector(Weakening(empty, -1)), clauses.imports ++ libImports)
      },
      goal = Set(1)
    )
    val proof = clausificationProofToProofCertificate(phase)
    assert(proof.conclusion == empty)
    KernelProof.assertCorrectProofNoSorry(proof, "distribution of truth and falsity")
    val exported = SctptpTest.checked(proof)
    assert(exported.steps.exists(_.isInstanceOf[SC.LeftFalse]))
    assert(exported.steps.last.isInstanceOf[SC.Cut])
  }

  test("reconstructing an imported empty clause concludes directly from that import") {
    val proof = Clausal.refute(Vector(empty)) match
      case success: Clausal.Outcome.Success => success.reconstructKernelProof
      case outcome => fail(s"Expected the input empty clause to refute, got $outcome")
    assert(proof.imports == Vector(empty))
    assert(proof.steps == Vector(Weakening(empty, -1)))
    assert(proof.conclusion == empty)
    KernelProof.assertCorrectProofNoSorry(proof, "imported empty clause")
    val exported = SctptpTest.checked(proof)
    assert(exported.steps.size == 1 && exported.steps.head.isInstanceOf[SC.Axiom])
  }

  test("the certified solver refutes falsity alone with either distribution strategy") {
    val problem = Problem(Vector(() |- bot), None)
    for mode <- Distribute.values do
      val proof = Prover.proveKernel(problem, clausifierOptions = ClausifierOptions(distribute = mode)).fold(outcome => fail(outcome.toString), identity)
      assert(proof.conclusion == empty)
      KernelProof.assertCorrectProofNoSorry(proof, s"refuting falsity with $mode")
  }
