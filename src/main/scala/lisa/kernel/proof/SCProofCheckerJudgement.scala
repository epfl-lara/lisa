package lisa.kernel.proof

/**
 * The judgement (or verdict) of a proof checking procedure.
 * Typically, see [[SCProofChecker.checkSingleSCStep]] and [[SCProofChecker.checkSCProof]].
 */
sealed abstract class SCProofCheckerJudgement {
    import SCProofCheckerJudgement.*

    /**
     * Whether this judgement is positive -- the proof is concluded to be valid;
     * or negative -- the proof checker couldn't certify the validity of this proof.
     * @return An instance of either [[SCValidProof]] or [[SCInvalidProof]]
     */
    def isValid: Boolean = this match {
        case SCValidProof => true
        case _: SCInvalidProof => false
    }
}

object SCProofCheckerJudgement {
    /**
     * A positive judgement.
     */
    case object SCValidProof extends SCProofCheckerJudgement

    /**
     * A negative judgement.
     * @param path The path of the error, expressed as indices
     * @param message The error message that hints about the first error encountered
     */
    case class SCInvalidProof(path: Seq[Int], message: String) extends SCProofCheckerJudgement
}
