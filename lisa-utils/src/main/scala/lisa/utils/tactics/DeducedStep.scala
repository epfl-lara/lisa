package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus._
import lisa.kernel.fol.FOL._

trait DeducedStep {
    val bot: Sequent
    val premises: Seq[Int]

    def asProofStep():SCProofStep

}

class InstantiateForall(original:Sequent, value:Term, t1:Int) extends DeducedStep{
    override val premises: Seq[Int] = Seq(t1)
    val bot: Sequent = ???
}