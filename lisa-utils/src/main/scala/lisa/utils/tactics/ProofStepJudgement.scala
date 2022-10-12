package lisa.utils.tactics
import ProofStepLib.ProofStep
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SequentCalculus.SCProofStep

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

object ProofStepJudgement{
  case class EarlyProofStepException(message: String) extends Exception(message)

  case class ValidProofStep(scps:SCProofStep) extends ProofStepJudgement

  case class InvalidProofStep(ps: ProofStep, message:String) extends ProofStepJudgement {
    def launch: Nothing = throw EarlyProofStepException(message)
  }

}
