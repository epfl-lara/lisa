package lisa.utils

import lisa.kernel.fol.FOL
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.{RunningTheoryJudgement, SCProof}
import lisa.utils.KernelHelpers.repr
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.*

import java.io.File

abstract class LisaException(errorMessage: String)(using val line: sourcecode.Line, val file: sourcecode.File) extends Exception(errorMessage) {
  def showError: String
}
object LisaException {
  case class InvalidKernelJustificationComputation(errorMessage: String, underlying: RunningTheoryJudgement.InvalidJustification[?], proof: Option[Library#Proof])(using
      sourcecode.Line,
      sourcecode.File
  ) extends LisaException(errorMessage) {
    def showError: String = "Construction of proof succedded, but the resulting proof or definition has been reported to be faulty. This may be due to an internal bug.\n" +
      "The resulting faulty event is:\n" +
      s"$underlying.message\n${underlying.error match {
          case Some(judgement) => FOLPrinter.prettySCProof(judgement)
          case None => ""
        }}"
  }
  
}

/**
 * Error made by the user, should be "explained"
 */
abstract class UserLisaException(var errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends LisaException(errorMessage) {
  def fixTrace(): Unit = ()
}
object UserLisaException {
  
  class UserParsingException(val parsedString: String, errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(errorMessage) {
    def showError: String = ""
  }

}
