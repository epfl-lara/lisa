package lisa.utils

import lisa.fol.FOL as F
import lisa.kernel.fol.FOL
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SCProof
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.KernelHelpers.repr

abstract class LisaException(errorMessage: String)(using val line: sourcecode.Line, val file: sourcecode.File) extends Exception(errorMessage) {
  def showError: String
}

import lisa.utils.KernelHelpers.{_, given}

import java.io.File
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

  class InvalidKernelAxiomException(errorMessage: String, name: String, formula: lisa.kernel.fol.FOL.Formula, theory: lisa.kernel.proof.RunningTheory)(using sourcecode.Line, sourcecode.File)
      extends LisaException(errorMessage) {
    def showError: String = s"The desired axiom \"$name\" contains symbol that are not part of the theory.\n" +
      s"The symbols {${theory.findUndefinedSymbols(formula)}} are undefined."
  }

}

/**
 * Error made by the user, should be "explained"
 */
abstract class UserLisaException(var errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends LisaException(errorMessage) {
  def fixTrace(): Unit = ()
}
object UserLisaException {
  class InvalidAxiomException(errorMessage: String, name: String, formula: lisa.fol.FOL.Formula, library: lisa.prooflib.Library)(using sourcecode.Line, sourcecode.File)
      extends UserLisaException(errorMessage) {
    def showError: String = s"The desired axiom \"$name\" contains symbol that are not part of the theory.\n" +
      s"The symbols {${library.theory.findUndefinedSymbols(formula.underlying)}} are undefined."
  }

  class UserParsingException(val parsedString: String, errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(errorMessage) {
    def showError: String = ""
  }

  class UndefinedSymbolException(errorMessage: String, symbol: F.ConstantLabel[?], library: lisa.prooflib.Library)(using sourcecode.Line, sourcecode.File) extends UserLisaException(errorMessage) {
    def showError: String = s"The desired symbol \"$symbol\" is unknown and has not been defined.\n"
  }

}
