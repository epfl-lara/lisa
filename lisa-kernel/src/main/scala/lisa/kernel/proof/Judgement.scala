package lisa.kernel.proof

import lisa.kernel.proof.RunningTheory

/**
 * The judgement (or verdict) of a proof checking procedure.
 * Typically, see [[SCProofChecker.checkSingleSCStep]] and [[SCProofChecker.checkSCProof]].
 */
sealed abstract class SCProofCheckerJudgement {
  import SCProofCheckerJudgement._
  val proof: SCProof

  /**
   * Whether this judgement is positive -- the proof is concluded to be valid;
   * or negative -- the proof checker couldn't certify the validity of this proof.
   * @return An instance of either [[SCValidProof]] or [[SCInvalidProof]]
   */
  def isValid: Boolean = this match {
    case _: SCValidProof => true
    case _: SCInvalidProof => false
  }
}

object SCProofCheckerJudgement {

  /**
   * A positive judgement.
   */
  case class SCValidProof(proof: SCProof, val usesSorry: Boolean = false) extends SCProofCheckerJudgement

  /**
   * A negative judgement.
   * @param path The path of the error, expressed as indices
   * @param message The error message that hints about the first error encountered
   */
  case class SCInvalidProof(proof: SCProof, path: Seq[Int], message: String) extends SCProofCheckerJudgement
}

/**
 * The judgement (or verdict) of a running theory.
 */
sealed abstract class RunningTheoryJudgement[+J <: RunningTheory#Justification] {
  import RunningTheoryJudgement._

  /**
   * Whether this judgement is positive -- the justification could be imported into the running theory;
   * or negative -- the justification is not suitable to be imported in the theory.
   * @return An instance of either [[ValidJustification]] or [[InvalidJustification]]
   */
  def isValid: Boolean = this match {
    case _: ValidJustification[_] => true
    case _: InvalidJustification[_] => false
  }
  def get: J = this match {
    case ValidJustification(just) => just
    case InvalidJustification(message, error) =>
      throw InvalidJustificationException(message, error)
  }
}

object RunningTheoryJudgement {

  /**
   * A positive judgement.
   */
  case class ValidJustification[J <: RunningTheory#Justification](just: J) extends RunningTheoryJudgement[J]

  /**
   * A negative judgement.
   * @param error If the justification is rejected because the proof is wrong, will contain the error in the proof.
   * @param message The error message that hints about the first error encountered
   */
  case class InvalidJustification[J <: RunningTheory#Justification](message: String, error: Option[SCProofCheckerJudgement.SCInvalidProof]) extends RunningTheoryJudgement[J]

  case class InvalidJustificationException(message: String, error: Option[SCProofCheckerJudgement.SCInvalidProof]) extends Exception(message)
}
