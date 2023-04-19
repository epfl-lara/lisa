package lisa.prooflib

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustificationException
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.*
import lisa.utils.*

/**
 * A helper file that provides various syntactic sugars for LISA's FOL and proofs. Best imported through utilities.Helpers
 * Usage:
 * <pre>
 * import utilities.Helpers.*
 * </pre>
 * or
 * <pre>
 * extends utilities.KernelHelpers.*
 * </pre>
 */
object TheoriesHelpers {
  export lisa.utils.KernelHelpers.{_, given}

  extension (just: RunningTheory#Justification) {

    /**
     * Outputs, with an implicit om.output function, a readable representation of the Axiom, Theorem or Definition.
     */
    def show(using om: OutputManager): just.type = {
      om.output(just.repr, Console.GREEN)
      just

    }
  }

  extension [J <: RunningTheory#Justification](theoryJudgement: RunningTheoryJudgement[J]) {

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def show(using om: OutputManager): Unit = {
      om.output(theoryJudgement.repr)
    }

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def showAndGet(using om: OutputManager): J = {
      theoryJudgement match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          just.show
        case InvalidJustification(message, error) =>
          om.output(s"$message\n${error match {
              case Some(judgement) => FOLPrinter.prettySCProof(judgement)
              case None => ""
            }}")
          om.finishOutput(InvalidJustificationException(message, error))
      }
    }
  }

  extension (proofJudgement: SCProofCheckerJudgement) {

    /**
     * If the SCProof is valid, show the inner proof and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def showAndGet(using om: OutputManager): SCProof = {
      proofJudgement match {
        case SCProofCheckerJudgement.SCValidProof(proof, _) =>
          om.output(FOLPrinter.prettySCProof(proofJudgement))
          proof
        case ip @ SCProofCheckerJudgement.SCInvalidProof(proof, path, message) =>
          om.output(s"$message\n${FOLPrinter.prettySCProof(proofJudgement)}")
          om.finishOutput(InvalidJustificationException("", Some(ip)))
      }
    }
  }

}
