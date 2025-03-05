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
    Variable("x", Ind),
    Variable("y", Ind),
    Variable("z", Ind),
    Variable("w", Ind),
    Variable("x1", Ind),
    Variable("y1", Ind),
    Variable("z1", Ind),
    Variable("w1", Ind)
  )

  protected val (s, t, u, v) = (Variable("s", Ind), Variable("t", Ind), Variable("u", Ind), Variable("v", Ind))

  def checkProof(proof: SCProof): Unit = {
    val judgement = checkSCProof(proof)
    assert(judgement.isValid, prettySCProof(judgement, true))
  }

  def checkProof(proof: SCProof, expected: Sequent): Unit = {
    val judgement = checkSCProof(proof)
    assert(judgement.isValid, "\n" + prettySCProof(judgement))
    assert(isSameSequent(proof.conclusion, expected), s"(${proof.conclusion.repr} did not equal ${expected.repr})")
  }

  inline def checkIncorrectProof(incorrectProof: SCProof): Unit = {
    assert(
      !checkSCProof(incorrectProof).isValid,
      s"(incorrect proof with conclusion '${incorrectProof.conclusion.repr}' was accepted by the proof checker)\nSequent: ${incorrectProof.conclusion}"
    )
  }
}
