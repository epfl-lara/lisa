package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.utils.Library
import lisa.utils.tactics.ProofStepLib.*
import lisa.utils.Parser.{parseFormula, parseSequent, parseTerm}

trait ProofsHelpers {
    library: Library & WithProofs =>
    given Library = library
    export BasicStepTactic.*
    export SimpleDeducedSteps.*
    private def proof: Proof = proofStack.head


    case class HaveSequent private[ProofsHelpers](bot:Sequent) {
        infix def by(just: ProofStepWithoutBot)(using String => Unit)(using finishOutput: Throwable => Nothing) : library.Proof#DoubleStep = {
            val r = just.asProofStep(bot)
            r.validate(library)
        }
    }

    case class AndThenSequent private[ProofsHelpers](bot:Sequent) {
        infix def by[N <: Int & Singleton](just: ProofStepWithoutBotNorPrem[N])(using String => Unit)(using finishOutput: Throwable => Nothing) : library.Proof#DoubleStep = {
            val r = just.asProofStepWithoutBot(Seq(proof.mostRecentStep._2)).asProofStep(bot)
            r.validate(library)
        }
    }

    /**
     * Claim the given Sequent as a ProofStep, which may require a justification by a proof tactic and premises.
     */
    def have(res:Sequent): HaveSequent = HaveSequent(res)
    /**
     * Claim the given Sequent as a ProofStep, which may require a justification by a proof tactic and premises.
     */
    def have(res:String): HaveSequent = HaveSequent(parseSequent(res))

    /**
     * Claim the given Sequent as a ProofStep directly following the previously proven tactic,
     * which may require a justification by a proof tactic.
     */
    def andThen(res:Sequent): AndThenSequent = AndThenSequent(res)
    /**
     * Claim the given Sequent as a ProofStep directly following the previously proven tactic,
     * which may require a justification by a proof tactic.
     */
    def andThen(res:String): AndThenSequent = AndThenSequent(parseSequent(res))

    /**
     * Import the given justification (Axiom, Theorem or Definition) into the current proof.
     */
    def withImport(just:theory.Justification):library.Proof#JustifiedImport = {
        proofStack.head.newJustifiedImport(just)

    }

    /**
     * Assume the given formula in all future left hand-side of claimed sequents.
     */
    def assume(f:Formula):Formula = {
        proofStack.head.addAssumption(f)
        f
    }

    /**
     * Store the given import and use it to discharge the proof of one of its assumption at the very end.
     */
    def endDischarge(ji: Library#Proof#JustifiedImport):Unit = {
        val p: Proof = proof
        if (p.validInThisProof(ji)){
            val p = proof
            p.addDischarge(ji.asInstanceOf[p.JustifiedImport])
        }
    }


    given Conversion[ProofStepWithoutBotNorPrem[0], ProofStepWithoutBot] = _.asProofStepWithoutBot(Seq())

}
