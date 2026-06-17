package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.* 

trait Tactico
trait SequentTactico:
  def apply(conclusion: Sequent): ProofJudgement
trait PremiseSequentTactico:
  def apply(conclusion: Sequent, premise: K.Thm): ProofJudgement

class HaveSequent(val statement: Sequent):
  infix def by(using lib: Library, proof: Proof)(tactic: SequentTactico): ProofJudgement = 
    val innerJudgement = tactic(statement)
    proof.absorb(innerJudgement)

class ThenHaveSequent(val statement: Sequent):
  infix def by(using lib: Library, proof: Proof)(tactic: PremiseSequentTactico): ProofJudgement = 
    proof.last match
      case Some(j) => 
        val innerJudgement = tactic(statement, j)
        proof.absorb(innerJudgement)
      case None =>
        // Handle the case where there is no last judgement
        proof.report(??? : ProofReport)
        ???

// so it is actually helpful to have these as separate,
// as when you are working on unit, then it actually does help
// to be able to have a silent failure mode instead of just
// being unable to continue on grounds of not having a value
// to generate?

class HaveMSequent(val statement: Sequent)

class ThenHaveMSequent(val statement: Sequent)



