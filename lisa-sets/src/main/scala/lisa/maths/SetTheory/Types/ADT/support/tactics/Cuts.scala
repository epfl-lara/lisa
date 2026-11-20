package lisa.maths.SetTheory.Types.ADT.support.tactics

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.ProofJudgement
import lisa.utils.prooflib.Subproof
import lisa.utils.prooflib.Thm

/**
 * Discharges matching premises with cuts and checks the final sequent.
 */
object Cuts {
  def apply(using proof: Proof, line: sourcecode.Line, file: sourcecode.File)(main: Thm)(sideFacts: Thm*)(bot: Sequent): ProofJudgement = Subproof {
    val combined = sideFacts.foldLeft(main) { (acc, fact) =>
      fact.right.find(r => acc.left.exists(l => isSame(l, r))) match
        case None => acc
        case Some(formula) =>
          val left = fact.left ++ acc.left.filterNot(isSame(_, formula))
          val right = fact.right.filterNot(isSame(_, formula)) ++ acc.right
          have(left |- right) by Cut.withParameters(formula)(fact, acc)
    }
    have(bot) by Weakening(combined)
  }
}
