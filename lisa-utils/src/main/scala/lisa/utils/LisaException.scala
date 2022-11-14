package lisa.utils
import lisa.kernel.proof.{RunningTheoryJudgement, SCProof}
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.utils.tactics.ProofTacticLib.ProofTactic
import lisa.utils.Helpers.repr

abstract class LisaException(errorMessage:String)(using val line: sourcecode.Line, val file:sourcecode.FileName) extends Exception(errorMessage) {
  def showError: String
}
object LisaException {
  case class InvalidKernelJustificationComputation(proof: Library#Proof, errorMessage: String, underlying: RunningTheoryJudgement.InvalidJustification[?])
                                             (using sourcecode.Line, sourcecode.FileName) extends LisaException(errorMessage) {
    def showError: String = "Construction of proof succedded, but the resulting proof or definition has been reported to be faulty. This may be due to an internal bug.\n" +
      "The resulting fauly proof is:\n" +
      s"$underlying.message\n${
        underlying.error match {
          case Some(judgement) => Printer.prettySCProof(judgement)
          case None => ""
        }
      }"
  }

  case class UnexpectedProofTacticFailureException(failure: Library#Proof#InvalidProofTactic, errorMessage: String)(using sourcecode.Line, sourcecode.FileName) extends LisaException(errorMessage) {
    def showError: String = "A proof tactic used in another proof tactic returned an unexpected error. This may indicate an implementation error in either of the two tactics.\n" +
      "Status of the proof at time of the error is:" +
      ProofPrinter.prettyProof(failure.proof)
  }
  /*
  class ProofStatusException(errorMessage: String)(using sourcecode.Line, sourcecode.FileName) extends LisaException(errorMessage){
    def showError: String = ""
  }*/

  class ParsingException(parsedString: String, errorMessage: String) extends LisaException(errorMessage) {
    def showError: String = ""
  }
}
/**
 * Error made by the user, should be "explained"
 */
abstract class UserLisaException(errorMessage:String)(using line: sourcecode.Line, file:sourcecode.FileName) extends LisaException(errorMessage)
object UserLisaException {
  class UnapplicableProofTactic(tactic:ProofTactic, errorMessage: String)(using sourcecode.Line, sourcecode.FileName) extends UserLisaException(errorMessage){
    def showError: String = s"Proof tactic ${tactic.name} used in $file:$line did not succeed:\n" +
      errorMessage
  }
  class UnimplementedProof(theorem: Library#THM)(using sourcecode.Line, sourcecode.FileName) extends LisaException("Unimplemented Theorem"){
    def showError: String = s"Theorem ${theorem.name}"
  }
  class UserParsingException(parsedString:String, errorMessage:String) extends UserLisaException(errorMessage){
    def showError: String = ""
  }
}
