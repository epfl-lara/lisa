package lisa.utils.tactics

import lisa.kernel.proof
import lisa.kernel.proof.{RunningTheory, RunningTheoryJudgement, SequentCalculus}
import lisa.kernel.proof.RunningTheoryJudgement.{InvalidJustification, InvalidJustificationException}
import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.utils.{Library, Printer}
import lisa.utils.tactics.ProofStepJudgement.*

object ProofStepLib {
  
  type Justification
  type DoubleStep = (ProofStep, SCProofStep)
  type JustifiedImport = (Sequent, RunningTheory#Justification)

  object Prev
  object SecondPrev
  type Index = Int | Prev.type | SecondPrev.type

  def indexToInt(current:Int, index:Index): Int = index match {
    case i:Int => i
    case Prev => current-1
    case SecondPrev => current-2
  }

  trait ProofStep{
    val premises: Seq[Index]
    def validate()(using l:Library)(using output: String => Unit)(using finishOutput: Throwable => Nothing) :Unit = {
      val prevs = l.currentProofSteps.head
      val references: Int => Sequent = prevs.getSequent
      val judgement = asSCProofStep(references, prevs.length)
      judgement match {
        case ValidProofStep(scps) => l.currentProofSteps = (prevs.addStep(this, scps))::l.currentProofSteps.tail
        case InvalidProofStep(ps, message) =>
          output(s"$message\n")
          finishOutput(EarlyProofStepException(message))
      }
    }

    def asSCProofStep(references: Int => Sequent, currentIndice:Int):ProofStepJudgement

  }

  trait ProofStepWithoutBot{
    val premises: Seq[Index]
    def asSCProofStep(bot: Sequent, references:Int => Sequent, currentIndice:Int): ProofStepJudgement
    def asProofStep(bot: Sequent): ProofStep = new ProofStepWithBot(this, bot)
  }

  class ProofStepWithBot(
                                                val underlying: ProofStepWithoutBot,
                                                val bot:Sequent
                                              ) extends ProofStep{
    override val premises: Seq[Index] = underlying.premises
    override def asSCProofStep(references: Int => Sequent, currentIndice:Int): ProofStepJudgement = underlying.asSCProofStep(bot, references, currentIndice)
  }

  trait ProofStepWithoutBotNorPrem[N <: Int & Singleton](val numbPrem: N)  {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], references:Int => Sequent): ProofStepJudgement
    def asProofStepWithoutBot(premises:Seq[Index]):ProofStepWithoutBot =
      new ProofStepWithoutBotWithPrem[N](this, premises)
  }


  class ProofStepWithoutBotWithPrem[N <: Int & Singleton](
                                                           val underlying: ProofStepWithoutBotNorPrem[N],
                                                           override val premises: Seq[Index]
                                                         ) extends ProofStepWithoutBot {
    val numbPrem: N = underlying.numbPrem
    def asSCProofStep(bot: Sequent, references:Int => Sequent, currentIndex:Int): ProofStepJudgement =
      underlying.asSCProofStep(bot, premises.map(indexToInt(currentIndex, _)), references)

  }

  given Conversion[SCProofStep, ProofStepJudgement] = ProofStepJudgement.ValidProofStep(_)



}
