package lisa.utils.tactics

import lisa.kernel.proof
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustificationException
import lisa.kernel.proof.SequentCalculus
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.Helpers.*
import lisa.utils.Library
import lisa.utils.OutputManager
import lisa.utils.Printer
import lisa.utils.tactics.ProofStepJudgement.*

object ProofStepLib {
  type Arity = Int & Singleton
  type ProofOfProofStepLib = Library#Proof

  /**
   * A proofstep is an object that relies on a step of premises and which can be translated into pure Sequent Calculus.
   */
  trait ProofStep {
    val proof:ProofOfProofStepLib
    val premises: Seq[proof.Fact]

    /**
     * Add the proofstep to the current proof of the given library.
     */
    def validate(l: Library)(using om:OutputManager): proof.DoubleStep = {
      proof.newDoubleStep(this.asInstanceOf)
    }

    /**
     * An abstract function transforming the ProofStep innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof: ProofStepJudgement

  }

  /**
   * A proof step lacking a bottom/conclusion sequent. Once given a conclusion sequent, it can become a ProofStep.
   */
  trait ProofStepWithoutBot {
    val proof:ProofOfProofStepLib
    type P = proof.type
    val premises: Seq[proof.Fact]

    /**
     * An abstract function transforming the ProofStepWithoutBot into a SCProofStep in pure Sequent Calculus,
     * by being given access to a target conclusive sequent and the current state of the proof.
     */
    def asSCProof(bot: Sequent): ProofStepJudgement

    /**
     * Gives a targeted bottom sequent, as a partial application towards the SC transformation.
     */
    def asProofStep(bot: Sequent): ProofStep{val proof:P} =
      (new ProofStepWithBot(this, bot)).asInstanceOf[ProofStep{val proof:P}]
  }

  /**
   * Intermediate datatype corresponding to a ProofStepWithoutBot once a targetted bottom sequent has been given to it.
   */
  class ProofStepWithBot protected[ProofStepLib] (
                                                     val underlying: ProofStepWithoutBot,
                                                     val givenBot: Sequent
                                                 ) extends ProofStep {
    val proof:underlying.proof.type = underlying.proof
    override val premises: Seq[proof.Fact] = underlying.premises
    override def asSCProof: ProofStepJudgement = underlying.asSCProof(givenBot ++< (proof.getAssumptions |- ()))
  }

  /**
   * Represent a ProofStep lacking the list of its premises, for partial application.
   */
  trait ProofStepWithoutPrem[N <: Arity](val numbPrem: N){
    val proof:ProofOfProofStepLib
    type P = proof.type

    /**
     * An abstract function transforming the ProofStepWithoutPrem innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof(premises: Seq[Int]): ProofStepJudgement

    /**
     * Gives the premises of the ProofStep, as a partial application towards the SC transformation.
     */
    def asProofStep(premises: Seq[proof.Fact]): ProofStep{val proof:P} =
      (new ProofStepWithPrem(this, premises)).asInstanceOf

    /**
     * Alias for [[asProofStep]]
     */
    def by(premises: Seq[proof.Fact]): ProofStep{val proof:P} = asProofStep(premises)
  }

  /**
   * Intermediate datatype corresponding to a [[ProofStepWithoutPrem]] once a sequence of premises has been given to it.
   */
  class ProofStepWithPrem[N <: Arity] protected[ProofStepLib] (
                                                      val underlying: ProofStepWithoutPrem[N],
                                                      _premises: Seq[underlying.proof.Fact]
                                                  ) extends ProofStep {
    val proof:underlying.proof.type = underlying.proof
    val premises: Seq[proof.Fact] = _premises.asInstanceOf[Seq[proof.Fact]]
    override def asSCProof: ProofStepJudgement =
      underlying.asSCProof(premises.map(prem => proof.sequentAndIntOfFact(prem)._2))
  }


  /**
   * A ProofStep without premises nor targeted bottom sequent.
   * Contains a tactic to reconstruct a partial Sequent Calculus proof if given those elements and the current proof.
   */
  trait ProofStepWithoutBotNorPrem[N <: Arity](val numbPrem:N){
    val proof:ProofOfProofStepLib
    type PP = proof.type

    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a list of premises, a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofStepJudgement
    def asProofStepWithoutBot(premises: Seq[proof.Fact]): ProofStepWithoutBot{val proof:PP} =
      (new ProofStepWithoutBotWithPrem[N](this, premises)).asInstanceOf[ProofStepWithoutBot{val proof:PP}]
    def apply(premises: proof.Fact*): ProofStepWithoutBot{val proof:PP} = asProofStepWithoutBot(premises)
  }

  /**
   * Intermediate datatype corresponding to a [[ProofStepWithoutBotNorPrem]] once a sequence of premises has been given to it.
   */
  class ProofStepWithoutBotWithPrem[N <: Arity] protected[ProofStepLib] (
                                                                                      val underlying: ProofStepWithoutBotNorPrem[N],
                                                                                      _premises: Seq[underlying.proof.Fact]
                                                                                  ) extends ProofStepWithoutBot {
    val proof : underlying.proof.type = underlying.proof
    val premises: Seq[proof.Fact] = _premises//.asInstanceOf[Seq[proof.Fact]]
    val numbPrem: N = underlying.numbPrem

    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent): ProofStepJudgement = {
      underlying.asSCProof(bot, premises.map(prem => proof.sequentAndIntOfFact(prem)._2))
    }
  }

  given Conversion[SCProofStep, ProofStepJudgement] = c => ProofStepJudgement.ValidProofStep(c)

}
