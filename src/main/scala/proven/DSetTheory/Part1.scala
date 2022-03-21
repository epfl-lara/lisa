package proven.DSetTheory
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.KernelHelpers.{*, given}
import lisa.kernel.Printer
import proven.tactics.ProofTactics.*
import proven.tactics.Destructors.*
import lisa.settheory.AxiomaticSetTheory.*

import scala.collection.immutable.SortedSet
import lisa.kernel.proof.{SCProof, SCProofChecker}

import scala.collection.immutable
object Part1 {

/**

 */
val noSetCOntainsItself: SCProof = {
    val contra = (y in y) <=> !(y in y)
    val s1 = Hypothesis(contra |- contra, contra)
    val s2 = LeftForall

}
}
