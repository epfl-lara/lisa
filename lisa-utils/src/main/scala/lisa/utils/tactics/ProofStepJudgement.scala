package lisa.utils.tactics
import ProofStepLib.ProofStep
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SequentCalculus.SCProofStep

sealed abstract class ProofStepJudgement {
  import ProofStepJudgement.*
  def isValid = this match {
    case ValidProofStep(scps) => true
    case InvalidProofStep(ps, error) => false
  }

}

object ProofStepJudgement{
  case class EarlyProofStepException(message: String) extends Exception(message)

  case class ValidProofStep(scps:SCProofStep) extends ProofStepJudgement
  case class InvalidProofStep(ps: ProofStep, message:String) extends ProofStepJudgement
}
