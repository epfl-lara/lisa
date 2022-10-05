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


    case class HaveSequent(bot:Sequent) {
        infix def by(just: ProofStepWithoutBot)(using String => Unit)(using finishOutput: Throwable => Nothing) : library.Proof#DoubleStep = {
            val r = just.asProofStep(bot)
            r.validate(library)
        }
        infix def by(just:library.theory.Axiom)(using String => Unit)(using finishOutput: Throwable => Nothing) :library.Proof#DoubleStep = {
            withImport(just)
            val ps = this.by(Rewrite(-library.proofStack.head.imports.length))
            ps
        }
    }

    case class AndThenSequent(bot:Sequent) {
        infix def by[N <: Int & Singleton](just: ProofStepWithoutBotNorPrem[N])(using String => Unit)(using finishOutput: Throwable => Nothing) : library.Proof#DoubleStep = {
            val r = just.asProofStepWithoutBot(Seq(Prev)).asProofStep(bot)
            r.validate(library)
        }
    }

    def have(res:Sequent): HaveSequent = HaveSequent(res)
    def have(res:String): HaveSequent = HaveSequent(parseSequent(res))

    def andThen(res:Sequent): AndThenSequent = AndThenSequent(res)
    def andThen(res:String): AndThenSequent = AndThenSequent(parseSequent(res))

    def withImport(just:theory.Axiom):library.Proof#JustifiedImport = {
        proofStack.head.JustifiedImport.newJustifiedImport(just)

    }

    def assume(f:Formula):Formula = {
        proofStack.head.addAssumption(f)
        f
    }




    extension[N <: Int & Singleton] (swbnp: ProofStepWithoutBotNorPrem[N]) {
        def apply(prem: Int*) :ProofStepWithoutBot = new ProofStepWithoutBotWithPrem[N](swbnp, prem)
    }


    given Conversion[ProofStepWithoutBotNorPrem[0], ProofStepWithoutBot] = _.asProofStepWithoutBot(Seq())

}
