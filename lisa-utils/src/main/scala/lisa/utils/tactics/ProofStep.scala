package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}

trait ProofStep {
  val premises: Seq[Int]

  def asSCProofStep(references: Int => Sequent):SCProofStep
}
