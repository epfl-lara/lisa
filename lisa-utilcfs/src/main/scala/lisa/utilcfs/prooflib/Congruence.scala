package lisa.utilcfs.prooflib

import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.ProofHelpers.{PremiseSequentTactic, SequentTactic}
import sourcecode.File
import sourcecode.Line

object Congruence extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  protected def prove(using File, Line)(using Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    Tautology.from(premises*)(conclusion)
