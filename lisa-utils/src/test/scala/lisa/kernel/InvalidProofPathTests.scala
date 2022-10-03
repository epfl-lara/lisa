package lisa.kernel

import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.*
import lisa.test.ProofCheckerSuite
import lisa.utils.Helpers.{*, given}

class InvalidProofPathTests extends ProofCheckerSuite {
  def checkPath(invalidProof: SCProof, expectedPath: Seq[Int]): Unit = {
    val proofCheckResult = SCProofChecker.checkSCProof(invalidProof)
    assert(!proofCheckResult.isValid, "expected invalid proof")
    assert(proofCheckResult.isInstanceOf[SCInvalidProof], "invalid proof but valid proof checker judgement")
    assert(proofCheckResult.asInstanceOf[SCInvalidProof].path === expectedPath)
  }

  test("incorrect step at top level") {
    val eq0 = RightRefl(() |- s === s, s === s)
    val eq1 = RightRefl(() |- t === t, t === t)
    val wrongStep2 = Weakening(s === s |- s === t, 0)
    val wrongStep3 = RightImplies(() |- (s === s) ==> (s === t), 1, s === s, s === t)
    checkPath(SCProof(eq0, eq1, wrongStep2, wrongStep3), Seq(2))
  }

  test("nested incorrect step") {
    val eq0 = RightRefl(() |- s === s, s === s)
    val wrongStep1 = Weakening(s === s |- s === t, 0)
    val erroneousSubproof = SCSubproof(SCProof(eq0, wrongStep1))
    val nestedSubproof = SCSubproof(SCProof(erroneousSubproof, eq0))
    checkPath(SCProof(eq0, eq0, eq0, nestedSubproof), Seq(3, 0, 1))
  }
}
