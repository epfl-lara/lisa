package lisa.utils.tactics

import lisa.kernel.proof
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.RunningTheoryJudgement.{InvalidJustification, InvalidJustificationException}
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.*
import lisa.utils.{Library, LisaException, OutputManager, Printer, UserLisaException}

object ProofTacticLib {
  type Arity = Int & Singleton

  /**
   * A ProofTactic is an object that relies on a step of premises and which can be translated into pure Sequent Calculus.
   */
  trait ProofTactic {
    val name: String = this.getClass.getSimpleName
    given ProofTactic = this

  }



/*

  /**
   * A proof step lacking a bottom/conclusion sequent. Once given a conclusion sequent, it can become a ProofTactic.
   */
  trait ProofTacticWithoutBot extends ProofTactic{

    def apply(using proof:Library#Proof)(a:Any*)(bot:Sequent): proof.ProofTacticJudgement
  }



  /**
   * Represent a ProofTactic lacking the list of its premises, for partial application.
   */
  trait ProofTacticWithoutPrem[N <: Arity](val numbPrem: N){
    val proof:ProofOfProofTacticLib
    type P = proof.type
    val nameWP: String = this.getClass.getSimpleName

    /**
     * An abstract function transforming the ProofTacticWithoutPrem innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof(givenPremises:Seq[proof.Fact]): proof.ProofTacticJudgement

    /**
     * Gives the premises of the ProofTactic, as a partial application towards the SC transformation.
     */
    def asProofTactic(premises: Seq[proof.Fact]): ProofTactic{val proof:P} =
      (new ProofTactic{
        override val proof: P = ProofTacticWithoutPrem.this.proof
        override val name: String = nameWP
        override def asSCProof: proof.ProofTacticJudgement = ProofTacticWithoutPrem.this.asSCProof(premises)
      }).asInstanceOf

    /**
     * Alias for [[asProofTactic]]
     */
    def by(premises: Seq[proof.Fact]): ProofTactic{val proof:P} = asProofTactic(premises)
  }



  /**
   * A ProofTactic without premises nor targeted bottom sequent.
   * Contains a tactic to reconstruct a partial Sequent Calculus proof if given those elements and the current proof.
   */
  trait ProofTacticWithoutBotNorPrem[N <: Arity](val numbPrem:N){
    val proof:ProofOfProofTacticLib
    type P = proof.type
    val nameWBNP: String = this.getClass.getSimpleName

    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a list of premises, a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement
    def asProofTacticWithoutBot(premises: Seq[proof.Fact]): ProofTacticWithoutBot{val proof:P} =
      (new ProofTacticWithoutBot[N]{
        override val proof: P = ProofTacticWithoutBotNorPrem.this.proof
        override val name: String = nameWBNP
        override def asSCProof(bot: Sequent): proof.ProofTacticJudgement = ProofTacticWithoutBotNorPrem.this.asSCProof(bot, premises)
      }).asInstanceOf

    def apply(premises: proof.Fact*): ProofTacticWithoutBot{val proof:PP} = asProofTacticWithoutBot(premises)
  }

  /**
   * Intermediate datatype corresponding to a [[ProofTacticWithoutBotNorPrem]] once a sequence of premises has been given to it.
   */
  class ProofTacticWithoutBotWithPrem[N <: Arity] protected[ProofTacticLib] (
                                                                                      val underlying: ProofTacticWithoutBotNorPrem[N],
                                                                                      givenPremises: Seq[underlying.proof.Fact],
                                                                                      override val nameWB: String
                                                                                  ) extends ProofTacticWithoutBot {
    val proof : underlying.proof.type = underlying.proof
    val numbPrem: N = underlying.numbPrem

    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent): proof.ProofTacticJudgement = {
      underlying.asSCProof(bot, givenPremises)
    }
  }
*/
}
