package lisa.utils.tactics
import lisa.utils.Library

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.fol.FOL
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.Helpers.{*, given}
import lisa.utils.tactics.ProofStepLib.{*, given}

object SimpleDeducedSteps {


  case object Trivial extends ProofStepWithoutBot with ProofStepWithoutBotNorPrem(1) {
    override val premises: Seq[Int] = Seq()
    def asSCProof(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement =
      SC.RewriteTrue(bot)

    def asSCProof(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Rewrite(bot, premises(0))

    }

  case class FormulaDischarge(f:FOL.Formula) extends ProofStepWithoutPrem {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val t1 = premises(0)
      val (lastStep, t2) = currentProof.mostRecentStep
      SC.Cut((lastStep.bot -< f) ++ (currentProof.getSequent(t1) -> f),
        t1,
        t2,
        f)
    }
  }

  case object Discharge extends ProofStepWithoutPrem {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val s = currentProof.getSequent(premises(0))
      if (s.right.size==1) {
        val f = s.right.head
        val t1 = premises(0)
        val (lastStep, t2) = currentProof.mostRecentStep
        SC.Cut((lastStep.bot -< f) ++ (currentProof.getSequent(t1) -> f),
          t1,
          t2,
          f)
      } else {
        ProofStepJudgement.InvalidProofStep(this.asProofStep(premises),
          "When discharging this way, the target sequent must have only a single formula on the right handside.")
      }
    }
    def apply(f:FOL.Formula): FormulaDischarge = FormulaDischarge(f)
    def apply(ij: Library#Proof#Fact)(using library:Library)(using String => Unit)(using finishOutput: Throwable => Nothing): Unit = {
      if (library.proofStack.head.validInThisProof(ij)){
        Discharge.asProofStep(Seq(ij)).validate(library)
      } else {
        val inv = ProofStepJudgement.InvalidProofStep(Discharge.asProofStep(Seq(ij)), "Illegal reference to justification from another proof in proofstep Discharge.")
        finishOutput(inv.launch)
      }
    }
  }

}
