package lisa.prooflib

import lisa.fol.FOL as F
import lisa.prooflib.*
import lisa.utils.K
import lisa.utils.Printer
import lisa.utils.UserLisaException

object ProofTacticLib {
  type Arity = Int & Singleton

  /**
   * A ProofTactic is an object that relies on a step of premises and which can be translated into pure Sequent Calculus.
   */
  trait ProofTactic {
    val name: String = this.getClass.getName.split('$').last
    given ProofTactic = this

  }

  trait OnlyProofTactic {
    def apply(using lib: Library, proof: lib.Proof): proof.ProofTacticJudgement
  }

  trait ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement
  }

  trait ProofFactTactic {
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact): proof.ProofTacticJudgement
  }
  trait ProofFactSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement
  }

  class UnapplicableProofTactic(val tactic: ProofTactic, val proof: Library#Proof, errorMessage: String)(using sourcecode.Line, sourcecode.File) extends UserLisaException(errorMessage) {
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
      Console.RED + proof.owningTheorem.prettyGoal + Console.RESET + "\n" +
        lisa.utils.ProofPrinter.prettyProof(proof, 2) + "\n" +
        "  " * (1 + proof.depth) + Console.RED + textline + Console.RESET + "\n\n" +
        s"   Proof tactic ${tactic.name} used in.(${file.value.split("/").last.split("\\\\").last}:${line.value}) did not succeed:\n" +
        "   " + errorMessage
    }
  }

  class UnimplementedProof(val theorem: Library#THM)(using sourcecode.Line, sourcecode.File) extends UserLisaException("Unimplemented Theorem") {
    def showError: String = s"Theorem ${theorem.name}"
  }
  case class UnexpectedProofTacticFailureException(failure: Library#Proof#InvalidProofTactic, errorMessage: String)(using sourcecode.Line, sourcecode.File)
      extends lisa.utils.LisaException(errorMessage) {
    def showError: String = "A proof tactic used in another proof tactic returned an unexpected error. This may indicate an implementation error in either of the two tactics.\n" +
      "Status of the proof at time of the error is:" +
      lisa.utils.ProofPrinter.prettyProof(failure.proof)
  }

}
