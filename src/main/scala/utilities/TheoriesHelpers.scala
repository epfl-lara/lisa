package utilities

import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.{RunningTheory, RunningTheoryJudgement, SCProof}
import lisa.kernel.proof.SequentCalculus.{Rewrite, isSameSequent}

object TheoriesHelpers {

  // for when the kernel will have a dedicated parser
  extension (theory: RunningTheory)
    def theorem(name: String, statement:String, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] = {
      val expected = proof.conclusion  // parse(statement)
      if ( expected == proof.conclusion) theory.makeTheorem(name, expected, proof, justifications)
      else if (isSameSequent(expected, proof.conclusion)) theory.makeTheorem(name, expected, proof.appended(Rewrite(expected, proof.length-1)), justifications)
      else InvalidJustification("The proof does not prove the claimed statement", None)
    }




}
