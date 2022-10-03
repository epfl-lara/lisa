package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, *}
import lisa.kernel.fol.FOL.*

trait ProofStepWithoutBot  {
    val premises: Seq[Int]
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep
    def asProofStep(bot: Sequent): ProofStep = ProofStepWithBot(asSCProofStep(bot, _), premises)

}

class ProofStepWithBot(val compile:(Int => Sequent) => SCProofStep,
                       override val premises: Seq[Int]
                      ) extends ProofStep{
    override def asSCProofStep(references: Int => Sequent): SCProofStep = compile(references)
}
