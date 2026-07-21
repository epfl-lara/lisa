package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.Helpers.*
import lisa.utils.prooflib.ProofHelpers.*

/**
 * Quantify all variables in a formula on the right side of the premise sequent.
 *
 * <pre>
 *         Γ ⊢ φ, Δ
 * -------------------------- x, y, ..., z do not appear in Γ
 *  Γ ⊢ ∀x.∀y. ... ∀z. φ, Δ
 * </pre>
 */
object Generalize extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  private def isQuantifiedOf(target: Expr[Prop], pivot: Expr[Prop], vars: List[Variable[Ind]] = Nil): Option[List[Variable[Ind]]] =
    target match
      case forall(x, inner) =>
        val next = x :: vars
        if isSame(inner, pivot) then Some(next) else isQuantifiedOf(inner, pivot, next)
      case _ => None

  private def invalid(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, message: String): ProofJudgement =
    ProofCarrier(Set(SoftError(message, file, line)), conclusion, None, ())

  def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    premises match
      case Seq(premise, _*) =>
        val difference = premise.statement.right.filterNot(conclusion.right.containsEq)
        if difference.isEmpty then BasicStep.Restate(conclusion, premise.kernel)
        else if difference.size > 1 then
          invalid(conclusion, s"There must be only one formula to quantify over between the premise and the conclusion. Found: \n${difference.mkString("\n")}")
        else
          val rdifference = conclusion.right.filterNot(premise.statement.right.containsEq)
          if rdifference.size != 1 then
            invalid(conclusion, s"There must be only one formula to quantify over between the premise and the conclusion. Found: \n${rdifference.mkString("\n")}")
          else
            val pivot = difference.head
            val target = rdifference.head
            val varsOption = isQuantifiedOf(target, pivot)

            if varsOption.isEmpty then invalid(conclusion, "Could not find a formula to quantify over in the conclusion.")
            else
              val vars = varsOption.get
              val conflicts = vars.toSet.intersect(premise.statement.left.flatMap(_.freeVars).collect { case v: Variable[Ind] @unchecked => v })

              if conflicts.nonEmpty then
                invalid(conclusion, s"Variable(s) ${conflicts.mkString(", ")} to be quantified appear in the LHS of the conclusion.")
              else
                // safe, proceed
                Subproof:
                  have(premise)

                  val base = premise.statement ->> pivot

                  vars.foldLeft(pivot): (pivot, v) =>
                    val quant = forall(v, pivot)
                    thenHave(base +>> quant) by BasicStep.RightForall.withParameters(pivot, v)
                    quant

                  thenHave(conclusion) by BasicStep.Restate.from(lastStep)
      case _ =>
        invalid(conclusion, "Generalize requires a premise.")
