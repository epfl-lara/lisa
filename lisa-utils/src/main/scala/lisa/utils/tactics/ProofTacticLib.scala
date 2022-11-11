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
import lisa.utils.{Library, LisaException, OutputManager, Printer, UserLisaException}

object ProofTacticLib {
  type Arity = Int & Singleton
  type ProofOfProofTacticLib = Library#Proof

  /**
   * A ProofTactic is an object that relies on a step of premises and which can be translated into pure Sequent Calculus.
   */
  trait ProofTactic {
    val proof:ProofOfProofTacticLib
    val name: String = this.getClass.getSimpleName

    /**
     * Add the ProofTactic to the current proof of the given library.
     */
    def validateUser(using line: sourcecode.Line, file: sourcecode.FileName): proof.ProofStep = {
      proof.newProofStep(this.asInstanceOf) match {
        case ps: proof.ProofStep => ps
        case proof.InvalidProofTactic(message) => throw UserLisaException.UnapplicableProofTactic(this, message)(using line, file)
      }
    }
    def validate: proof.ProofStep = validateUser

    /*
    def validateInTactic: proof.ProofStep = {
      proof.newProofStep(this.asInstanceOf) match {
        case ps: proof.ProofStep => ps
        case InvalidProofTactic(message) => throw LisaException.FaultyDeepProofTacticException(this, message)
      }
    }*/

    /**
     * An abstract function transforming the ProofTactic innto a SCProofStep in pure Sequent Calculus.
     */
    def asSCProof: proof.ProofTacticJudgement

  }

  /**
   * A proof step lacking a bottom/conclusion sequent. Once given a conclusion sequent, it can become a ProofTactic.
   */
  trait ProofTacticWithoutBot {
    val proof:ProofOfProofTacticLib
    type P = proof.type
    val nameWB: String = this.getClass.getSimpleName
    /**
     * An abstract function transforming the ProofTacticWithoutBot into a SCProofStep in pure Sequent Calculus,
     * by being given access to a target conclusive sequent and the current state of the proof.
     */
    def asSCProof(bot: Sequent): proof.ProofTacticJudgement

    /**
     * Gives a targeted bottom sequent, as a partial application towards the SC transformation.
     */
    def asProofTactic(bot: Sequent): ProofTactic{val proof:P} =
      (new ProofTacticWithBot(this, bot, nameWB)).asInstanceOf[ProofTactic{val proof:P}]
  }

  /**
   * Intermediate datatype corresponding to a ProofTacticWithoutBot once a targetted bottom sequent has been given to it.
   */
  class ProofTacticWithBot protected[ProofTacticLib] (
                                                     val underlying: ProofTacticWithoutBot,
                                                     val givenBot: Sequent,
                                                     override val name: String
                                                 ) extends ProofTactic {
    val proof:underlying.proof.type = underlying.proof
    override def asSCProof: proof.ProofTacticJudgement = underlying.asSCProof(givenBot ++< (proof.getAssumptions |- ()))
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
      (new ProofTacticWithPrem(this, premises, nameWP)).asInstanceOf

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
                                                      givenPremises: Seq[underlying.proof.Fact],
                                                      override val name: String
                                                  ) extends ProofTactic {
    val proof:underlying.proof.type = underlying.proof
    override def asSCProof: proof.ProofTacticJudgement =
      underlying.asSCProof(givenPremises)
  }


  /**
   * A ProofTactic without premises nor targeted bottom sequent.
   * Contains a tactic to reconstruct a partial Sequent Calculus proof if given those elements and the current proof.
   */
  trait ProofTacticWithoutBotNorPrem[N <: Arity](val numbPrem:N){
    val proof:ProofOfProofTacticLib
    type PP = proof.type
    val nameWBNP: String = this.getClass.getSimpleName

    /**
     * Contains a tactic to reconstruct a partial Sequent Calculus proof if given
     * a list of premises, a targeted bottom sequent and the current proof.
     */
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement
    def asProofTacticWithoutBot(premises: Seq[proof.Fact]): ProofTacticWithoutBot{val proof:PP} =
      (new ProofTacticWithoutBotWithPrem[N](this, premises, nameWBNP)).asInstanceOf

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

  given step2Judgement(using proof:Library#Proof): Conversion[SCProofStep, proof.ProofTacticJudgement] = c => ??? //ProofTacticJudgement.ValidProofTactic[F](Seq(c))

}
