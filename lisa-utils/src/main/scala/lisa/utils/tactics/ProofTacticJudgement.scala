package lisa.utils.tactics

import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.utils.tactics.ProofTacticLib.ProofTactic

/**
 * Contains the result of a tactic computing a SCProofTactic.
 * Can be successful or unsuccessful.
 */
sealed abstract class ProofTacticJudgement {
  import ProofTacticJudgement.*

  /**
   * Returns true if and only if the jusdgement is valid.
   */
  def isValid: Boolean = this match {
    case ValidProofTactic(scps) => true
    case InvalidProofTactic(error) => false
  }

}

object ProofTacticJudgement {

  /**
   * Indicates an error in the building of a proof that was caught before the proof is passed to the logical kernel.
   * May indicate a faulty tactic application.
   */
  case class EarlyProofTacticException(message: String) extends Exception(message)

  /**
   * A Sequent Calculus proof step that has been correctly produced.
   */
  case class ValidProofTactic(scps: SCProofStep) extends ProofTacticJudgement

  /**
   * A proof step which led to an error when computing the corresponding Sequent Calculus proof step.
   */
  case class InvalidProofTactic(message: String) extends ProofTacticJudgement {
    def launch: Nothing = throw EarlyProofTacticException(message)
  }

}
