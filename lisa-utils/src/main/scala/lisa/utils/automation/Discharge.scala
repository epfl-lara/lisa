package lisa.utils.automation

import lisa.utils.K
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofCarrier.Failure
import lisa.utils.prooflib.ProofJudgement

object Discharge:
  private def dischargeOne(using library: Library)(current: Thm, discharge: Thm): ProofJudgement =
    if discharge.statement.right.size != 1 then Failure("Discharge premises must have exactly one right formula.")
    else
      val formula = discharge.statement.right.head
      current.statement.left.find(isSame(_, formula)) match
        case None => ProofJudgement(current)
        case Some(matchedFormula) =>
          val remaining = current.statement.left.filterNot(isSame(_, matchedFormula))
          val conclusion = Sequent(remaining ++ discharge.statement.left, current.statement.right)
          if conclusion == current.statement then ProofJudgement(current)
          else
            K.Cut(using library.theory)(conclusion.underlying, discharge.kernel, current.kernel, formula.underlying) match
              case Right(thm) => ProofJudgement(Thm(conclusion, thm))
              case Left(err) => Failure(s"Discharge could not cut premise: $err")

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*)(base: Thm): ProofJudgement =
    premises
      .foldLeft(ProofJudgement(base)): (current, nextPrem) =>
        current.flatMap((_, theorem) => dischargeOne(theorem, nextPrem))
