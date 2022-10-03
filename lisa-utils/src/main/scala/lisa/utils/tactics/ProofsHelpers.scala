package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}

trait ProofsHelpers {
    val N: BasicStepTactic.type = BasicStepTactic
    export SimpleDeducedSteps.*


    case class HaveSequent(bot:Sequent) {

        infix def by(just: ProofStepWithoutBot): ProofStep = just.asProofStep(bot)
    }

    def have(bot:Sequent): HaveSequent = HaveSequent(bot)



}
