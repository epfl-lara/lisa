package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers._
import lisa.utils.prooflib.TacticHelpers.failWith

/**
 * Instantiates a sequence of universal binders while preserving the premise context.
 */
object InstantiateForallSeq:
  def apply(using Library, sourcecode.File, sourcecode.Line)(args: Seq[Expr[Ind]])(fact: Thm)(bot: Sequent): ProofJudgement =
    if fact.right.size != 1 then ProofCarrier(Set(SoftError("InstantiateForallSeq requires exactly one right-hand formula.", summon[sourcecode.File], summon[sourcecode.Line])), bot, None, ())
    else if args.isEmpty then BasicStep.Weakening(bot, fact.kernel)
    else InstantiateForall(args*)(bot, fact)

/**
 * Introduces a sequence of quantifiers around one formula on either side of a sequent.
 */
object QuantifiersIntro:
  def apply(using Library, sourcecode.File, sourcecode.Line)(vars: Seq[Variable[Ind]])(fact: Thm)(bot: Sequent): ProofJudgement = Subproof {
    val added = bot -- fact.statement
    val removed = fact.statement -- bot
    if vars.isEmpty || (added.left.isEmpty && added.right.isEmpty && removed.left.isEmpty && removed.right.isEmpty) then have(bot) by BasicStep.Restate.from(fact)
    else
      val onLeft = added.left.size == 1 && removed.left.size == 1 && added.right.isEmpty && removed.right.isEmpty
      val onRight = added.right.size == 1 && removed.right.size == 1 && added.left.isEmpty && removed.left.isEmpty
      if !onLeft && !onRight then failWith("QuantifiersIntro requires exactly one formula to be replaced on the same side.")
      val source = if onLeft then removed.left.head else removed.right.head
      val target = if onLeft then added.left.head else added.right.head
      val (quantify, step): ((Variable[Ind], Expr[Prop]) => Expr[Prop], (Sequent, Thm) => ProofJudgement) =
        (onLeft, target) match
          case (true, forall(_, _)) => ((v, body) => forall(v, body), (s: Sequent, t: Thm) => BasicStep.LeftForall(s, t.kernel))
          case (true, exists(_, _)) => ((v, body) => exists(v, body), (s: Sequent, t: Thm) => BasicStep.LeftExists(s, t.kernel))
          case (false, forall(_, _)) => ((v, body) => forall(v, body), (s: Sequent, t: Thm) => BasicStep.RightForall(s, t.kernel))
          case (false, exists(_, _)) => ((v, body) => exists(v, body), (s: Sequent, t: Thm) => BasicStep.RightExists(s, t.kernel))
          case _ => failWith("QuantifiersIntro requires a quantified target formula.")
      val (result, _) = vars.foldRight((fact, source)) { case (variable, (current, formula)) =>
        val quantified = quantify(variable, formula)
        val conclusion =
          if onLeft then (fact.left - source + quantified) |- fact.right
          else fact.left |- (fact.right - source + quantified)
        val next = have(conclusion) by (goal => step(goal, current))
        (next, quantified)
      }
      have(bot) by BasicStep.Restate.from(result)
  }
