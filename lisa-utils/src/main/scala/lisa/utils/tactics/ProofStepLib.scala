package lisa.utils.tactics

import lisa.kernel.proof
import lisa.kernel.proof.RunningTheoryJudgement.{InvalidJustification, InvalidJustificationException}
import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.proof.{RunningTheory, RunningTheoryJudgement, SequentCalculus}
import lisa.utils.Helpers.*
import lisa.utils.tactics.ProofStepJudgement.*
import lisa.utils.{Library, Printer}

object ProofStepLib {



  /**
   * A proofstep is an object that relies on a step of premises and which can be translated into pure Sequent Calculus.
   */
  trait ProofStep{
    val premises: Seq[Library#Proof#Fact]

    /**
     * Add the proofstep to the current proof of the given library.
     */
    def validate(l:Library)(using output: String => Unit)(using finishOutput: Throwable => Nothing): l.Proof#DoubleStep = {
      l.proofStack.head.newDoubleStep(this)
    }

    /**
     * An abstract function transforming the ProofStep innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof(currentProof: Library#Proof):ProofStepJudgement

  }

  /**
   * A proof step lacking a bottom/conclusion sequent. Once given a conclusion sequent, it can become a ProofStep.
   */
  trait ProofStepWithoutBot{
    val premises: Seq[Library#Proof#Fact]
    /**
     * An abstract function transforming the ProofStepWithoutBot into a SCProofStep in pure Sequent Calculus,
     * by being given access to a target conclusive sequent and the current state of the proof.
     */
    def asSCProof(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement

    /**
     * Gives a targeted bottom sequent, as a partial application towards the SC transformation.
     */
    def asProofStep(bot: Sequent): ProofStep = new ProofStepWithBot(this, bot)
  }

  /**
   * Intermediate datatype corresponding to a ProofStepWithoutBot once a targetted bottom sequent has been given to it.
   */
  class ProofStepWithBot protected[ProofStepLib](
                          val underlying: ProofStepWithoutBot,
                          val givenBot:Sequent
                        ) extends ProofStep{
    override val premises: Seq[Library#Proof#Fact] = underlying.premises
    override def asSCProof(currentProof: Library#Proof): ProofStepJudgement = underlying.asSCProof(givenBot ++< (currentProof.getAssumptions|-()), currentProof)
  }

  /**
   * Represent a ProofStep lacking the list of its premises, for partial application.
   */
  trait ProofStepWithoutPrem{
    /**
     * An abstract function transforming the ProofStepWithoutPrem innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement

    /**
     * Gives the premises of the ProofStep, as a partial application towards the SC transformation.
     */
    def asProofStep(premises: Seq[Library#Proof#Fact]): ProofStep = new ProofStepWithPrem(this, premises)
    /**
     * Alias for [[asProofStep]]
     */
    def by(premises: Seq[Library#Proof#Fact]): ProofStep = asProofStep(premises)
  }

  /**
   * Intermediate datatype corresponding to a [[ProofStepWithoutPrem]] once a sequence of premises has been given to it.
   */
  class ProofStepWithPrem protected[ProofStepLib](
                          val underlying: ProofStepWithoutPrem,
                          val premises: Seq[Library#Proof#Fact]
                        ) extends ProofStep{
    override def asSCProof(currentProof: Library#Proof): ProofStepJudgement =
      if (premises.forall(prem => currentProof.validInThisProof(prem))) {
        underlying.asSCProof(premises.map(prem => currentProof.getSequentAndInt(prem.asInstanceOf[currentProof.Fact])._2), currentProof)
      }
      else {
        ProofStepJudgement.InvalidProofStep(this, "Illegal reference to a previous step outside of this Proof's scope.")
      }
  }

  /**
   * A ProofStep without premises nor targeted bottom sequent.
   * Contains a tactic to reconstruct a partial Sequent Calculus proof if given those elements and the current proof.
   */
  trait ProofStepWithoutBotNorPrem[N <: Int & Singleton](val numbPrem: N)  {
    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a list of premises, a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement
    def asProofStepWithoutBot(premises:Seq[Library#Proof#Fact]):ProofStepWithoutBot =
      new ProofStepWithoutBotWithPrem[N](this, premises)
    def apply(premises:Library#Proof#Fact*) :ProofStepWithoutBot = asProofStepWithoutBot(premises)
  }

  /**
   * Intermediate datatype corresponding to a [[ProofStepWithoutBotNorPrem]] once a sequence of premises has been given to it.
   */
  class ProofStepWithoutBotWithPrem[N <: Int & Singleton] protected[ProofStepLib](
                                                           val underlying: ProofStepWithoutBotNorPrem[N],
                                                           override val premises: Seq[Library#Proof#Fact]
                                                         ) extends ProofStepWithoutBot {
    val numbPrem: N = underlying.numbPrem
    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement = {
      if (premises.forall(prem => currentProof.validInThisProof(prem))) {
        underlying.asSCProof(bot, premises.map(prem => currentProof.getSequentAndInt(prem.asInstanceOf[currentProof.Fact])._2), currentProof)
      }
      else {
        ProofStepJudgement.InvalidProofStep(asProofStep(bot), "Illegal reference to a previous step outside of this Proof's scope.")
      }
    }
  }

  given Conversion[SCProofStep, ProofStepJudgement] = c => ProofStepJudgement.ValidProofStep(c)



}
