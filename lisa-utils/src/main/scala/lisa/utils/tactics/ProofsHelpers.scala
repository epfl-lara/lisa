package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.utils.tactics.ProofStepLib.*
import lisa.utils.Parser.{parseTerm, parseFormula, parseSequent}

object ProofsHelpers {
    export BasicStepTactic.*
    export SimpleDeducedSteps.*


    case class HaveSequent(bot:Sequent) {

        infix def by(just: ProofStepWithoutBot): ProofStep = just.asProofStep(bot)
    }

    def have(res:Sequent): HaveSequent = HaveSequent(res)
    def have(res:String): HaveSequent = HaveSequent(parseSequent(res))


    extension[N <: Int & Singleton] (swbnp: ProofStepWithoutBotNorPrem[N]) {
        def apply(prem: Int*) :ProofStepWithoutBot = new ProofStepWithoutBotWithPrem[N](swbnp, prem)
    }

    given Conversion[ProofStepWithoutBotNorPrem[0], ProofStepWithoutBot] = _.asProofStepWithoutBot(Seq())

}
