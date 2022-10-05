package lisa.utilities.prooftransform
import lisa.kernel.proof.SCProof
import lisa.utils.Helpers.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.fol.FOL.*
import lisa.utils.Printer

case class  ProofInstantiationRemover(pr : SCProof)  extends ProofTransformer(pr) {
    
    private val adjMat = adjacencyMatrix(pr.steps, s => s.premises)

    //PUBLIC FUNCTIONS###################################################################################################################

    def transform() : SCProof = instsAsImports(pr)

    //PRIVATE FUNCTIONS##################################################################################################################    
    /**
     * determines if a step is a problematic instantiation that should be transformed into an import
     *
     * @param step the step to check for
     * @return whether the given step is an Instantiation tha thas a link to an import
     */
    private def isInst(step : SCProofStep) : Boolean = step match {
          case InstPredSchema(_, t, _) => true
          case _ => false
        }

    /**
     * Maps Instantiations to Rewrites of imports
     * 
     * @return a proof where all instantiations are rewrites of imports
     */
    private def instsAsImports(pr : SCProof) : SCProof = {
        val mSteps = pr.steps.zipWithIndex.map((s, j) => s match {
          case _ if isInst(s) => Hypothesis(sequentToFormula(s.bot) |- sequentToFormula(s.bot), sequentToFormula(s.bot))
          case _ => s
        })
        
        SCProof(mSteps, pr.imports)
    }
}
