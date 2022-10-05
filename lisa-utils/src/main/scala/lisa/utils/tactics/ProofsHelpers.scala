package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.utils.Library
import lisa.utils.tactics.ProofStepLib.*
import lisa.utils.Parser.{parseFormula, parseSequent, parseTerm}

object ProofsHelpers {
    export BasicStepTactic.*
    export SimpleDeducedSteps.*


    case class HaveSequent(bot:Sequent) {
        infix def by(just: ProofStepWithoutBot)(using l:Library): ProofStep = just.asProofStep(bot)
    }

    case class AndThenSequent(bot:Sequent) {
        infix def by[N <: Int & Singleton](just: ProofStepWithoutBotNorPrem[N])(using l:Library): ProofStep = just.asProofStepWithoutBot(Seq(Prev)).asProofStep(bot)
    }

    def have(res:Sequent): HaveSequent = HaveSequent(res)
    def have(res:String): HaveSequent = HaveSequent(parseSequent(res))

    def andThen(res:Sequent): AndThenSequent = AndThenSequent(res)
    def andThen(res:String): AndThenSequent = AndThenSequent(parseSequent(res))


    extension[N <: Int & Singleton] (swbnp: ProofStepWithoutBotNorPrem[N]) {
        def apply(prem: Int*) :ProofStepWithoutBot = new ProofStepWithoutBotWithPrem[N](swbnp, prem)
    }

    given Conversion[ProofStepWithoutBotNorPrem[0], ProofStepWithoutBot] = _.asProofStepWithoutBot(Seq())

}
