package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.tactics.ProofStepLib.{*, given}

object SimpleDeducedSteps {

    case object Trivial extends ProofStepWithoutBot with ProofStepWithoutBotNorPrem(1) {
      override val premises: Seq[Int] = Seq()
      def asSCProofStep(bot: Sequent, references:Int => Sequent, currentIndex:Int): ProofStepJudgement =
        SC.RewriteTrue(bot)

      def asSCProofStep(bot: Sequent, premises:Seq[Int], references:Int => Sequent): ProofStepJudgement =
        SC.Rewrite(bot, premises(0))

    }

}
