package lisa.utils.tactics

import lisa.kernel.proof
import lisa.kernel.proof.{RunningTheory, RunningTheoryJudgement, SequentCalculus}
import lisa.kernel.proof.RunningTheoryJudgement.{InvalidJustification, InvalidJustificationException}
import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.utils.{Library, Printer}
import lisa.utils.tactics.ProofStepJudgement.*
import lisa.utils.Helpers.*

object ProofStepLib {


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
    def validate(l:Library)(using output: String => Unit)(using finishOutput: Throwable => Nothing): l.Proof#DoubleStep = {
      l.proofStack.head.DoubleStep.newDoubleStep(this)
    }

    def asSCProofStep(currentProof: Library#Proof):ProofStepJudgement

  }

  trait ProofStepWithoutBot{
    val premises: Seq[Index]
    def asSCProofStep(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement
    def asProofStep(bot: Sequent): ProofStep = new ProofStepWithBot(this, bot)
  }

  class ProofStepWithBot(
                                                val underlying: ProofStepWithoutBot,
                                                val givenBot:Sequent
                                              ) extends ProofStep{
    override val premises: Seq[Index] = underlying.premises
    override def asSCProofStep(currentProof: Library#Proof): ProofStepJudgement = underlying.asSCProofStep(givenBot ++< (currentProof.assumptions|-()), currentProof)
  }

  trait ProofStepWithoutBotNorPrem[N <: Int & Singleton](val numbPrem: N)  {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement
    def asProofStepWithoutBot(premises:Seq[Index]):ProofStepWithoutBot =
      new ProofStepWithoutBotWithPrem[N](this, premises)
  }


  class ProofStepWithoutBotWithPrem[N <: Int & Singleton](
                                                           val underlying: ProofStepWithoutBotNorPrem[N],
                                                           override val premises: Seq[Index]
                                                         ) extends ProofStepWithoutBot {
    val numbPrem: N = underlying.numbPrem
    def asSCProofStep(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement =
      underlying.asSCProofStep(bot, premises.map(indexToInt(currentProof.length, _)), currentProof: Library#Proof)

  }

  given Conversion[SCProofStep, ProofStepJudgement] = ProofStepJudgement.ValidProofStep(_)



}
