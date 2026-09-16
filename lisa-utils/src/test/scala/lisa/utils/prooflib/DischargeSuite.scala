package lisa.utils.prooflib

import lisa.kernel.proof.{RunningTheory, SCProofChecker}
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.SimpleDeducedSteps.Discharge
import org.scalatest.funsuite.AnyFunSuite

class DischargeSuite extends AnyFunSuite:
  private object TestLibrary extends Library:
    val theory = new RunningTheory

  import TestLibrary.*
  private given TestLibrary.type = TestLibrary
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val p, q = variable[Prop]
  private val truth = Theorem(⊤) { have(thesis) by Restate }
  private val base = Theorem((⊤, p) |- p) { have(thesis) by Hypothesis }
  private val identity = Theorem(p |- p) { have(thesis) by Hypothesis }
  private val unrelated = Theorem(q |- q) { have(thesis) by Hypothesis }

  test("cut a known formula without searching for a pivot"):
    val proof = new BaseProof(base.asInstanceOf[THMFromProof])
    given proof.type = proof
    val result = have(Discharge(truth)(base))
    assert(result.statement == (p |- p))
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("skip absent and unchanged discharges"):
    val proof = new BaseProof(base.asInstanceOf[THMFromProof])
    given proof.type = proof
    val result = have(Discharge(unrelated, identity)(base))
    assert(result.statement == base.statement)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("reject a discharge with multiple conclusions"):
    val both = Theorem(p |- (p, q)) { have(thesis) by Hypothesis }
    val proof = new BaseProof(base.asInstanceOf[THMFromProof])
    given proof.type = proof
    assert(!Discharge(both)(base).isValid)
