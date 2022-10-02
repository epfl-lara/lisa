package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus._
import lisa.kernel.fol.FOL._

trait DeducedStepTactic {
    val premises: Seq[Int]

    def asProofStep(bot:Sequent, references: Int => Sequent):SCProofStep


}

class InstantiateForall(val t1:Int) extends DeducedStep{
    override val premises: Seq[Int] = Seq(t1)
    override def asProofStep(bot: Sequent, references: Int => Sequent): SCProofStep = ???
}

class BasicStepTactic(scStep:SCProofStep) extends DeducedStepTactic {
    val premises = scStep.premises

    override def asProofStep(bot: Sequent, references: Int => Sequent): SCProofStep = scStep
}


class ProofStep(val bot: Sequent, val tact: DeducedStepTactic) {
}



given Conversion[SCProofStep, ProofStep] = ProofStep(_.bot, DeducedStepTactic)