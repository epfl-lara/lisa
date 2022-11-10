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
import lisa.utils.tactics.ProofTacticJudgement.*

object ProofTacticLib {
  type Arity = Int & Singleton
  type ProofOfProofTacticLib = Library#Proof

  /**
   * A ProofTactic is an object that relies on a step of premises and which can be translated into pure Sequent Calculus.
   */
  trait ProofTactic {
    val proof:ProofOfProofTacticLib
    val premises: Seq[proof.Fact]

    /**
     * Add the ProofTactic to the current proof of the given library.
     */
    def validate(using om:OutputManager): proof.ProofStep = {
      proof.newProofStep(this.asInstanceOf)
    }

    /**
     * An abstract function transforming the ProofTactic innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof(premMap: proof.Fact => Int): ProofTacticJudgement

  }

  /**
   * A proof step lacking a bottom/conclusion sequent. Once given a conclusion sequent, it can become a ProofTactic.
   */
  trait ProofTacticWithoutBot {
    val proof:ProofOfProofTacticLib
    type P = proof.type
    val premises: Seq[proof.Fact]

    /**
     * An abstract function transforming the ProofTacticWithoutBot into a SCProofStep in pure Sequent Calculus,
     * by being given access to a target conclusive sequent and the current state of the proof.
     */
    def asSCProof(premMap: proof.Fact => Int, bot: Sequent): ProofTacticJudgement

    /**
     * Gives a targeted bottom sequent, as a partial application towards the SC transformation.
     */
    def asProofTactic(bot: Sequent): ProofTactic{val proof:P} =
      (new ProofTacticWithBot(this, bot)).asInstanceOf[ProofTactic{val proof:P}]
  }

  /**
   * Intermediate datatype corresponding to a ProofTacticWithoutBot once a targetted bottom sequent has been given to it.
   */
  class ProofTacticWithBot protected[ProofTacticLib] (
                                                     val underlying: ProofTacticWithoutBot,
                                                     val givenBot: Sequent
                                                 ) extends ProofTactic {
    val proof:underlying.proof.type = underlying.proof
    override val premises: Seq[proof.Fact] = underlying.premises
    override def asSCProof(premMap: proof.Fact => Int): ProofTacticJudgement = underlying.asSCProof(premMap, givenBot ++< (proof.getAssumptions |- ()))
  }

  /**
   * Represent a ProofTactic lacking the list of its premises, for partial application.
   */
  trait ProofTacticWithoutPrem[N <: Arity](val numbPrem: N){
    val proof:ProofOfProofTacticLib
    type P = proof.type

    /**
     * An abstract function transforming the ProofTacticWithoutPrem innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof(premises:Seq[Int]): ProofTacticJudgement

    /**
     * Gives the premises of the ProofTactic, as a partial application towards the SC transformation.
     */
    def asProofTactic(premises: Seq[proof.Fact]): ProofTactic{val proof:P} =
      (new ProofTacticWithPrem(this, premises)).asInstanceOf

    /**
     * Alias for [[asProofTactic]]
     */
    def by(premises: Seq[proof.Fact]): ProofTactic{val proof:P} = asProofTactic(premises)
  }

  /**
   * Intermediate datatype corresponding to a [[ProofTacticWithoutPrem]] once a sequence of premises has been given to it.
   */
  class ProofTacticWithPrem[N <: Arity] protected[ProofTacticLib] (
                                                      val underlying: ProofTacticWithoutPrem[N],
                                                      _premises: Seq[underlying.proof.Fact]
                                                  ) extends ProofTactic {
    val proof:underlying.proof.type = underlying.proof
    val premises: Seq[proof.Fact] = _premises.asInstanceOf[Seq[proof.Fact]]
    override def asSCProof(premMap: proof.Fact => Int): ProofTacticJudgement =
      underlying.asSCProof(premises.map(premMap))
  }


  /**
   * A ProofTactic without premises nor targeted bottom sequent.
   * Contains a tactic to reconstruct a partial Sequent Calculus proof if given those elements and the current proof.
   */
  trait ProofTacticWithoutBotNorPrem[N <: Arity](val numbPrem:N){
    val proof:ProofOfProofTacticLib
    type PP = proof.type

    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a list of premises, a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement
    def asProofTacticWithoutBot(premises: Seq[proof.Fact]): ProofTacticWithoutBot{val proof:PP} =
      (new ProofTacticWithoutBotWithPrem[N](this, premises)).asInstanceOf[ProofTacticWithoutBot{val proof:PP}]
    def apply(premises: proof.Fact*): ProofTacticWithoutBot{val proof:PP} = asProofTacticWithoutBot(premises)
  }

  /**
   * Intermediate datatype corresponding to a [[ProofTacticWithoutBotNorPrem]] once a sequence of premises has been given to it.
   */
  class ProofTacticWithoutBotWithPrem[N <: Arity] protected[ProofTacticLib] (
                                                                                      val underlying: ProofTacticWithoutBotNorPrem[N],
                                                                                      _premises: Seq[underlying.proof.Fact]
                                                                                  ) extends ProofTacticWithoutBot {
    val proof : underlying.proof.type = underlying.proof
    val premises: Seq[proof.Fact] = _premises//.asInstanceOf[Seq[proof.Fact]]
    val numbPrem: N = underlying.numbPrem

    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a targeted bottom sequent and the current proof.
     */
    def asSCProof(premMap: proof.Fact => Int, bot: Sequent): ProofTacticJudgement = {
      underlying.asSCProof(bot, premises.map(premMap))
    }
  }

  given Conversion[SCProofStep, ProofTacticJudgement] = c => ProofTacticJudgement.ValidProofTactic(c)

}
