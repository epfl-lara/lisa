package lisa.utils.tactics
import lisa.utils.Library

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.tactics.ProofStepLib.{*, given}

object SimpleDeducedSteps {

    case object Trivial extends ProofStepWithoutBot with ProofStepWithoutBotNorPrem(1) {
      override val premises: Seq[Int] = Seq()
      def asSCProofStep(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement =
        SC.RewriteTrue(bot)

      def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
        SC.Rewrite(bot, premises(0))

    }

}
