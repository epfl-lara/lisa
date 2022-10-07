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
    val premises: Seq[Library#Proof#InnerJustification]
    def validate(l:Library)(using output: String => Unit)(using finishOutput: Throwable => Nothing): l.Proof#DoubleStep = {
      l.proofStack.head.DoubleStep.newDoubleStep(this)
    }

    def asSCProofStep(currentProof: Library#Proof):ProofStepJudgement

  }

  trait ProofStepWithoutBot{
    val premises: Seq[Library#Proof#InnerJustification]
    def asSCProofStep(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement
    def asProofStep(bot: Sequent): ProofStep = new ProofStepWithBot(this, bot)
  }

  class ProofStepWithBot(
                          val underlying: ProofStepWithoutBot,
                          val givenBot:Sequent
                        ) extends ProofStep{
    override val premises: Seq[Library#Proof#InnerJustification] = underlying.premises
    override def asSCProofStep(currentProof: Library#Proof): ProofStepJudgement = underlying.asSCProofStep(givenBot ++< (currentProof.getAssumptions|-()), currentProof)
  }

  trait ProofStepWithoutPrem{
    def asSCProofStep(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement
    def asProofStep(premises: Seq[Library#Proof#InnerJustification]): ProofStep = new ProofStepWithPrem(this, premises)
    def by(premises: Seq[Library#Proof#InnerJustification]): ProofStep = asProofStep(premises)
  }

  class ProofStepWithPrem(
                          val underlying: ProofStepWithoutPrem,
                          val premises: Seq[Library#Proof#InnerJustification]
                        ) extends ProofStep{
    override def asSCProofStep(currentProof: Library#Proof): ProofStepJudgement =
      if (premises.forall(prem => currentProof.validInThisProof(prem))) {
        underlying.asSCProofStep(premises.map(prem => currentProof.getSequentAndInt(prem.asInstanceOf[currentProof.InnerJustification])._2), currentProof)
      }
      else {
        ProofStepJudgement.InvalidProofStep(this, "Illegal reference to a previous step outside of this Proof's scope.")
      }
  }

  trait ProofStepWithoutBotNorPrem[N <: Int & Singleton](val numbPrem: N)  {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement
    def asProofStepWithoutBot(premises:Seq[Library#Proof#InnerJustification]):ProofStepWithoutBot =
      new ProofStepWithoutBotWithPrem[N](this, premises)
    def apply(premises:Library#Proof#InnerJustification*) :ProofStepWithoutBot = asProofStepWithoutBot(premises)
  }


  class ProofStepWithoutBotWithPrem[N <: Int & Singleton](
                                                           val underlying: ProofStepWithoutBotNorPrem[N],
                                                           override val premises: Seq[Library#Proof#InnerJustification]
                                                         ) extends ProofStepWithoutBot {
    val numbPrem: N = underlying.numbPrem
    def asSCProofStep(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement = {
      if (premises.forall(prem => currentProof.validInThisProof(prem))) {
        underlying.asSCProofStep(bot, premises.map(prem => currentProof.getSequentAndInt(prem.asInstanceOf[currentProof.InnerJustification])._2), currentProof)
      }
      else {
        ProofStepJudgement.InvalidProofStep(asProofStep(bot), "Illegal reference to a previous step outside of this Proof's scope.")
      }
    }
  }

  given Conversion[SCProofStep, ProofStepJudgement] = ProofStepJudgement.ValidProofStep(_)



}
