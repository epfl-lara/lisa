package lisa.prooflib

import lisa.kernel.proof
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustificationException
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.KernelHelpers.*
import lisa.prooflib.*
import lisa.utils.{Printer, UserLisaException}

object ProofTacticLib {
  type Arity = Int & Singleton

  /**
   * A ProofTactic is an object that relies on a step of premises and which can be translated into pure Sequent Calculus.
   */
  trait ProofTactic {
    val name: String = this.getClass.getName.split('$').last
    given ProofTactic = this

  }

  trait ParameterlessHave {
    def apply(using proof: Library#Proof)(bot: Sequent): proof.ProofTacticJudgement
  }

  trait ParameterlessAndThen {
    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement
  }

  class UnapplicableProofTactic(val tactic: ProofTactic, proof: Library#Proof, errorMessage: String)(using sourcecode.Line, sourcecode.File) extends UserLisaException(errorMessage) {
    override def fixTrace(): Unit = {
      val start = getStackTrace.indexWhere(elem => {
        !elem.getClassName.contains(tactic.name)
      }) + 1
      setStackTrace(getStackTrace.take(start))
    }

    def showError: String = {
      val source = scala.io.Source.fromFile(file.value)
      val textline = source.getLines().drop(line.value - 1).next().dropWhile(c => c.isWhitespace)
      source.close()
      Console.RED + proof.owningTheorem.repr + Console.RESET + "\n" +
        lisa.utils.ProofPrinter.prettyProof(proof, 2) + "\n" +
        "  " * (1 + proof.depth) + Console.RED + textline + Console.RESET + "\n\n" +
        s"   Proof tactic ${tactic.name} used in.(${file.value.split("/").last.split("\\\\").last}:${line.value}) did not succeed:\n" +
        "   " + errorMessage
    }
  }

  class UnimplementedProof(val theorem: Library#THM)(using sourcecode.Line, sourcecode.File) extends UserLisaException("Unimplemented Theorem") {
    def showError: String = s"Theorem ${theorem.name}"
  }
  case class UnexpectedProofTacticFailureException(failure: Library#Proof#InvalidProofTactic, errorMessage: String)
                                                  (using sourcecode.Line, sourcecode.File) extends lisa.utils.LisaException(errorMessage) {
    def showError: String = "A proof tactic used in another proof tactic returned an unexpected error. This may indicate an implementation error in either of the two tactics.\n" +
      "Status of the proof at time of the error is:" +
      lisa.utils.ProofPrinter.prettyProof(failure.proof)
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
