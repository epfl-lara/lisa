package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}

object ProofStepLib {

  trait ProofStep{
    val premises: Seq[Int]
    def asSCProofStep(references: Int => Sequent):SCProofStep
  }

  trait ProofStepWithoutBot{
    val premises: Seq[Int]
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep
    def asProofStep(bot: Sequent): ProofStep = new ProofStepWithBot(this, bot)
  }

  class ProofStepWithBot(
                                                val underlying: ProofStepWithoutBot,
                                                val bot:Sequent
                                              ) extends ProofStep{
    override val premises: Seq[Int] = underlying.premises
    override def asSCProofStep(references: Int => Sequent): SCProofStep = underlying.asSCProofStep(bot, references)
  }

  trait ProofStepWithoutBotNorPrem[N <: Int & Singleton](val numbPrem: N)  {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], references:Int => Sequent): SCProofStep
    def asProofStepWithoutBot(premises:Seq[Int]):ProofStepWithoutBot =
      new ProofStepWithoutBotWithPrem[N](this, premises)
  }


  class ProofStepWithoutBotWithPrem[N <: Int & Singleton](
                                                           val underlying: ProofStepWithoutBotNorPrem[N],
                                                           override val premises: Seq[Int]
                                                         ) extends ProofStepWithoutBot {
    val numbPrem: N = underlying.numbPrem
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      underlying.asSCProofStep(bot, premises, references)

  }



}
