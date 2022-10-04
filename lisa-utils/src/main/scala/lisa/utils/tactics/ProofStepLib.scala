package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.utils.Library

object ProofStepLib {
  object Prev
  object SecondPrev
  type Index = Int | Prev.type | SecondPrev.type
  def indexToInt(current:Int, index:Index): Int = index match {
    case i:Int => i
    case Prev => current-1
    case SecondPrev => current-2
  }

  trait ProofStep(using l:Library){
    l.currentProofSteps = (this::l.currentProofSteps.head)::l.currentProofSteps.tail
    val premises: Seq[Index]
    def asSCProofStep(references: Int => Sequent, currentIndice:Int):SCProofStep
  }

  trait ProofStepWithoutBot{
    val premises: Seq[Index]
    def asSCProofStep(bot: Sequent, references:Int => Sequent, currentIndice:Int): SCProofStep
    def asProofStep(bot: Sequent)(using l:Library): ProofStep = new ProofStepWithBot(this, bot)
  }

  class ProofStepWithBot(using l:Library)(
                                                val underlying: ProofStepWithoutBot,
                                                val bot:Sequent
                                              ) extends ProofStep{
    override val premises: Seq[Index] = underlying.premises
    override def asSCProofStep(references: Int => Sequent, currentIndice:Int): SCProofStep = underlying.asSCProofStep(bot, references, currentIndice)
  }

  trait ProofStepWithoutBotNorPrem[N <: Int & Singleton](val numbPrem: N)  {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], references:Int => Sequent): SCProofStep
    def asProofStepWithoutBot(premises:Seq[Index]):ProofStepWithoutBot =
      new ProofStepWithoutBotWithPrem[N](this, premises)
  }


  class ProofStepWithoutBotWithPrem[N <: Int & Singleton](
                                                           val underlying: ProofStepWithoutBotNorPrem[N],
                                                           override val premises: Seq[Index]
                                                         ) extends ProofStepWithoutBot {
    val numbPrem: N = underlying.numbPrem
    def asSCProofStep(bot: Sequent, references:Int => Sequent, currentIndex:Int): SCProofStep =
      underlying.asSCProofStep(bot, premises.map(indexToInt(currentIndex, _)), references)

  }



}
