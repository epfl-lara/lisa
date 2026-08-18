package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL._

object Discharge:
  private def dischargeOne(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(current: Thm, discharge: Thm): Either[ProofError, Thm] =
    if discharge.statement.right.size != 1 then Left(SoftError("Discharge premises must have exactly one right formula.", file, line))
    else
      val formula = discharge.statement.right.head
      current.statement.left.find(isSame(_, formula)) match
        case None => Right(current)
        case Some(matchedFormula) =>
          val conclusion = Sequent((current.statement.left - matchedFormula) ++ discharge.statement.left, current.statement.right)
          K.Cut(using library.theory)(conclusion.underlying, discharge.kernel, current.kernel, formula.underlying) match
            case Right(thm) => Right(Thm(conclusion, thm))
            case Left(err) => Left(SoftError(s"Discharge could not cut premise: $err", file, line))

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*)(base: Thm): ProofJudgement =
    premises
      .foldLeft(Right(base): Either[ProofError, Thm]): (current, nextPrem) =>
        current.flatMap(dischargeOne(using file, line)(using library)(_, nextPrem))
      .fold(
        error => ProofCarrier(Set(error), base.statement, None, ()),
        thm => ProofJudgement(thm)
      )
