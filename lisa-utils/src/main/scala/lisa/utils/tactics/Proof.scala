package lisa.utils.tactics

import lisa.kernel.proof.SCProof


case class Proof(steps: IndexedSeq[ProofStep], imports: IndexedSeq[Sequent] = IndexedSeq.empty) {
    def numberedSteps: Seq[(ProofStep, Int)] = steps.zipWithIndex

    def apply(i: Int): ProofStep = {
        if (i >= 0)
            if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
            else steps(i)
        else throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
    }

    def getSequent(i: Int): Sequent = {
        if (i >= 0)
            if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
            else steps(i).bot
        else {
            val i2 = -(i + 1)
            if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
            else imports(i2)
        }
    }

    def toSCProof:SCProof = {
        Proof(steps.map(ps => ps.tact.asProofStep(ps.bot, steps.getSequent)))
    }


    def length: Int = steps.length

}

object Proof {

    /**
     * Instantiates a proof from an indexed list of proof steps.
     * @param steps the steps of the proof
     * @return the corresponding proof
     */
    def apply(steps: ProofStep*): Proof = {
        Proof(steps.toIndexedSeq)
    }

}
