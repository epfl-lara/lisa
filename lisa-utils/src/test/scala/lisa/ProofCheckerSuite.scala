package lisa.test

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus.isSameSequent
import lisa.utils.KernelHelpers.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

abstract class ProofCheckerSuite extends AnyFunSuite {

  import lisa.kernel.fol.FOL.*

  protected val (x, y, z, w, xp, yp, zp, wp) = (
    Variable("x", Term),
    Variable("y", Term),
    Variable("z", Term),
    Variable("w", Term),
    Variable("x1", Term),
    Variable("y1", Term),
    Variable("z1", Term),
    Variable("w1", Term)
  )

  protected val (s, t, u, v) = (Variable("s", Term), Variable("t", Term), Variable("u", Term), Variable("v", Term))

  def checkProof(proof: SCProof): Unit = {
    val judgement = checkSCProof(proof)
    assert(judgement.isValid, prettySCProof(judgement, true))
  }

  def checkProof(proof: SCProof, expected: Sequent): Unit = {
    val judgement = checkSCProof(proof)
    assert(judgement.isValid, "\n" + prettySCProof(judgement))
    assert(isSameSequent(proof.conclusion, expected), s"(${proof.conclusion.repr} did not equal ${expected.repr})")
  }

  def checkIncorrectProof(incorrectProof: SCProof): Unit = {
    assert(
      !checkSCProof(incorrectProof).isValid,
      s"(incorrect proof with conclusion '${incorrectProof.conclusion.repr}' was accepted by the proof checker)\nSequent: ${incorrectProof.conclusion}"
    )
  }
}
