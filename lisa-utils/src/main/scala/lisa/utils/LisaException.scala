package lisa.utils
import lisa.utils.tactics.ProofTacticJudgement

abstract class LisaException(errorMessage:String) extends Exception(errorMessage) {

}

object LisaException {

  case class InvalidKernelJustificationComputation(errorMessage: String, underlying:lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification[?]) extends LisaException(errorMessage)
  case class FaultyProofTacticException(tactic:ProofTacticJudgement, errorMessage: String) extends LisaException(errorMessage)
  case class ProofStatusException(errorMessage: String) extends LisaException(errorMessage)
  case class EmptyProofException(errorMessage: String) extends LisaException(errorMessage)

  case class ParsingException(parsedString:String, errorMessage:String) extends LisaException(errorMessage) {
  }
}
