package lisa.utils

abstract class LisaException(errorMessage:String) extends Exception(errorMessage) {

}

object LisaException {

  class InvalidKernelJustificationComputation(errorMessage: String, underlying:lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification[?]) extends LisaException(errorMessage)
  class FaultyProofStepException(errorMessage: String) extends LisaException(errorMessage)
  class ProofStatusException(errorMessage: String) extends LisaException(errorMessage)
  class EmptyProofException(errorMessage: String) extends LisaException(errorMessage)

  class ParsingException(parsedString:String, errorMessage:"String") extends LisaException(errorMessage) {
  }
}
