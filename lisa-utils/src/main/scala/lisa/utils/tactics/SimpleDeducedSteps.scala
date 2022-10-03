package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.proof.SequentCalculus as SC

object SimpleDeducedSteps {

    case class Trivial(t1: Int) extends ProofStepWithoutBot {
        override val premises: Seq[Int] = Seq(t1)
        def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
            SC.Rewrite(bot, t1)
    }
    //def Trivial: ProofStepWithoutBot = ???

}
