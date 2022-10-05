package lisa.utilities.prooftransform
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.*
import lisa.utils.Printer

/**
 * A transformation that ensures its result is a proof where no instantiaiton are left, rreplaced by imports and rewrites of their conclusion
 *
 * @param pr the proof to be modified
 */
case class ProofInstantiationRemover(pr: SCProof) extends ProofTransformer(pr) {

  private val adjMat = adjacencyMatrix(pr.steps, s => s.premises)
  private val neg_premises = dependency_finder(pr.steps, ps => ps.premises.filter(_ >= 0).map(pr.steps(_)), ps => ps.premises)

  // PUBLIC FUNCTIONS###################################################################################################################
  /**
   * Maps a proof to a new proof where Instantiations are replaced by hypothesis
   *
   * @return the modified proof
   */
  def transform(): SCProof = instsAsImports(pr)

  // PRIVATE FUNCTIONS##################################################################################################################
  /**
   * determines if a step is a problematic instantiation that should be transformed into an import
   *
   * @param step the step to check for
   * @return whether the given step is an Instantiation tha thas a link to an import
   */
  private def isInst(step: SCProofStep): Boolean = step match {
    case InstPredSchema(_, t, _) if !neg_premises.getOrElse(step, Seq.empty).isEmpty => true
    case InstFunSchema(_, t, _) if !neg_premises.getOrElse(step, Seq.empty).isEmpty => true
    case _ => false
  }

  /**
   * Maps Instantiations to Rewrites of imports
   *
   * @return a proof where all instantiations are rewrites of imports
   */
  private def instsAsImports(pr: SCProof): SCProof = {
    val imps = pr.steps.zipWithIndex.filter((st, j) => isInst(st)).map(_._2).zipWithIndex

    val mImps = imps.toMap
    val mSteps = pr.steps.zipWithIndex.map((s, j) =>
      s match {
        case _ if isInst(s) => Rewrite(() |- sequentToFormulaNullable(s.bot), -pr.imports.length - mImps(j) - 1)
        case _ => s
      }
    )

    SCProof(mSteps, pr.imports ++ imps.map((j, i) => mSteps(j).bot))
  }

}
