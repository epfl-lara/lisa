package lisa.utils.tactics

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.Library
import lisa.utils.tactics.ProofStepLib.{DoubleStep, JustifiedImport}

trait WithProofs extends ProofsHelpers {
  library: Library =>

  case class Proof(steps: List[DoubleStep], imports: List[JustifiedImport] = Nil) {
    //def numberedSteps: Seq[(DoubleStep, Int)] = steps.zipWithIndex

    def apply(i: Int): DoubleStep = {
      if (i >= 0)
        if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
        else steps(steps.length-i-1)
      else throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
    }

    def getSequent(i: Int): Sequent = {
      if (i >= 0)
        if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
        else steps(steps.length-i-1)._2.bot
      else {
        val i2 = -(i + 1)
        if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
        else imports(imports.length+i)._1
      }
    }

    def toSCProof:SCProof = {
      SCProof(steps.map(_._2).reverse.toIndexedSeq, imports.map(_._1).toIndexedSeq)
    }


    def length: Int = steps.length

    def addStep(ds:DoubleStep):Proof = Proof(steps=ds::steps, imports)
    def addImport(ji:JustifiedImport):Proof = Proof(steps, imports=ji::imports)

  }

  object Proof {

    /**
     * Instantiates a proof from an indexed list of proof steps.
     * @param steps the steps of the proof
     * @return the corresponding proof
     */
    def apply(steps: DoubleStep*): Proof= {
      Proof(steps.toList, Nil)
    }

    def empty = Proof(Nil, Nil)

  }


}
