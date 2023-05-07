package lisa.prooflib

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

  extension (just: K.RunningTheory#Justification) {

    /**
     * Outputs, with an implicit om.output function, a readable representation of the Axiom, Theorem or Definition.
     */
    def show(using om: OutputManager): just.type = {
      just match {
        case j: K.RunningTheory#Theorem =>
          if (j.withSorry) om.output(j.repr, Console.YELLOW)
          else om.output(j.repr, Console.GREEN)
        case j: K.RunningTheory#FunctionDefinition =>
          if (j.withSorry) om.output(j.repr, Console.YELLOW)
          else om.output(j.repr, Console.GREEN)
        case _ => om.output(just.repr, Console.GREEN)
      }
      just
    }
  }

  extension [J <: K.RunningTheory#Justification](theoryJudgement: K.Judgement[J]) {

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
        case K.ValidJustification(just) =>
          just.show
        case K.InvalidJustification(message, error) =>
          om.output(s"$message\n${error match {
              case Some(judgement) => FOLPrinter.prettySCProof(judgement)
              case None => ""
            }}")
          om.finishOutput(K.InvalidJustificationException(message, error))
      }
    }
  }

  extension (proofJudgement: K.SCProofCheckerJudgement) {

    /**
     * If the SCProof is valid, show the inner proof and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def showAndGet(using om: OutputManager): K.SCProof = {
      proofJudgement match {
        case K.SCProofCheckerJudgement.SCValidProof(proof, _) =>
          om.output(FOLPrinter.prettySCProof(proofJudgement))
          proof
        case ip @ K.SCProofCheckerJudgement.SCInvalidProof(proof, path, message) =>
          om.output(s"$message\n${FOLPrinter.prettySCProof(proofJudgement)}")
          om.finishOutput(K.InvalidJustificationException("", Some(ip)))
      }
    }
  }

}
