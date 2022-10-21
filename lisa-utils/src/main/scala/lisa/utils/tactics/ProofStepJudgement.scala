package lisa.utils.tactics

import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.utils.tactics.ProofStepLib.ProofStep

/**
 * Contains the result of a tactic computing a SCProofStep.
 * Can be successful or unsuccessful.
 */
sealed abstract class ProofStepJudgement {
  import ProofStepJudgement.*

  /**
   * Returns true if and only if the jusdgement is valid.
   */
  def isValid: Boolean = this match {
    case ValidProofStep(scps) => true
    case InvalidProofStep(ps, error) => false
  }

}

object ProofStepJudgement {

  /**
   * Indicates an error in the building of a proof that was caught before the proof is passed to the logical kernel.
   * May indicate a faulty tactic application.
   */
  case class EarlyProofStepException(message: String) extends Exception(message)

  /**
   * A Sequent Calculus proof step that has been correctly produced.
   */
  case class ValidProofStep(scps: SCProofStep) extends ProofStepJudgement

  /**
   * A proof step which led to an error when computing the corresponding Sequent Calculus proof step.
   */
  case class InvalidProofStep(ps: ProofStep, message: String) extends ProofStepJudgement {
    def launch: Nothing = throw EarlyProofStepException(message)
  }

}
