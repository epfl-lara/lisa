package lisa.utils
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.utils.tactics.ProofTacticJudgement
import lisa.utils.tactics.ProofTacticLib.ProofTactic
import lisa.utils.Helpers.repr

abstract class LisaException(errorMessage:String)(using val line: sourcecode.Line, val file:sourcecode.Name) extends Exception(errorMessage) {
  def showError: String

}

object LisaException {

  case class InvalidKernelJustificationComputation(errorMessage: String, underlying:RunningTheoryJudgement.InvalidJustification[?])
                                                  (using sourcecode.Line, sourcecode.Name) extends LisaException(errorMessage) {
    def showError: String = "Construction of proof succedded, but the resulting proof or definition has been reported to be faulty. This may be due to an internal bug.\n" +
        "The resulting fauly proof is:\n" +
        s"$underlying.message\n${underlying.error match {
          case Some(judgement) => Printer.prettySCProof(judgement)
          case None => ""
        }}"

  }
  case class FaultyUserProofTacticException(tactic:ProofTactic, errorMessage: String)(using sourcecode.Line, sourcecode.Name) extends LisaException(errorMessage){
    def showError: String = s"Proof tactic ${tactic.name} used in $file:$line did not succeed:\n" +
        errorMessage
  }

  case class FaultyDeepProofTacticException(tactic:ProofTactic, errorMessage: String)(using sourcecode.Line, sourcecode.Name) extends LisaException(errorMessage){
    def showError: String = "A proof tactic used in another proof tactic returned an unexpected error. This may indicate an implementation error in either of the two tactics.\n" +
        "Status of the proof at time of the error is:" +
        ProofPrinter.prettyProof(tactic.proof)
  }
  /*
  case class ProofStatusException(errorMessage: String)(using sourcecode.Line, sourcecode.Name) extends LisaException(errorMessage){
    def showError: String = ""
  }*/
  case class EmptyProofException(errorMessage: String)(using sourcecode.Line, sourcecode.Name) extends LisaException(errorMessage){
    def showError: String = ""
  }

  case class ParsingException(parsedString:String, errorMessage:String) extends LisaException(errorMessage){
    def showError: String = ""
  }
}
