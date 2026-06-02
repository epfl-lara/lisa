package lisa.maths.SetTheory.Types.ADTv2.support.core

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.{
  ProofFactSequentTactic,
  ProofTactic
}

object QuantifiersIntro extends lisa.utils.prooflib.ProofTacticLib.ProofTactic {

  /**
   *  Executes the tactic on a specific goal.
   *
   *  @param lib the library that is currently being used
   *  @param proof the ongoing proof in which the tactic is called
   *  @param vars the variables that needs to be quantified
   *  @param fact the proof of the sequent without quantification
   *  @param bot the statement to prove
   */
  def apply(using
      lib: lisa.utils.prooflib.Library,
      proof: lib.Proof,
      line: sourcecode.Line, 
      file: sourcecode.File
  )(
      vars: Seq[Variable[Ind]]
  )(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof { sp ?=>

    def restateDirectly(summary: String) =
      TacticErrors.attemptOrInvalid(using lib)(proof)(
        tacticName = "QuantifiersIntro",
        summary = summary,
        factStatement = fact.statement,
        bot = bot,
        "Variables requested" -> vars.mkString(", ")
      ) {
        lib.have(bot) by Restate.from(fact)
      } match
        case Left(judgement) => judgement
        case Right(value)    => value

    def foldQuantifiers(
      fWithoutQuant: Expr[Prop],
      mkBot: Expr[Prop] => Sequent,
      side: String,
      mkFormulaAndTactic: ((Variable[Ind], Expr[Prop]) => Expr[Prop], ProofFactSequentTactic & ProofTactic)
    ): (sp.Fact, Expr[Prop]) =
      vars.foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
        val (mkFormula, tactic) = mkFormulaAndTactic
        val (accFact, accFormula) = acc
        val newFormula = mkFormula(v, accFormula)
        (
          TacticErrors.wrapUnapplicable(using lib)(sp)(
            tactic = this,
            summary = s"${tactic.name} failed while introducing `$v` on the $side side",
            factStatement = fact.statement,
            bot = bot,
            "Variables requested" -> vars.mkString(", "),
            "Side" -> side,
            "Current formula" -> accFormula.toString,
            "Target formula" -> newFormula.toString
          ) {
            lib.have(mkBot(newFormula)) by tactic(accFact)
          },
          newFormula
        )
      }

    if vars.isEmpty then
      restateDirectly("no variables were requested, so the tactic expected a direct restatement")
    else
      val diff: Sequent = bot -- fact.statement

      diff match
        case Sequent(s, _) if s.size == 1 =>
          val diffRest = bot.left -- s
          val changedFormula = s.head

          foldQuantifiers(
            (fact.statement.left -- diffRest).head,
            newFormula => diffRest + newFormula |- bot.right,
            "left",
            changedFormula match
              case ∀(_, _) => ((v, phi) => ∀(v, phi), LeftForall)
              case ∃(_, _) => ((v, phi) => ∃(v, phi), LeftExists)
              case _ =>
                return TacticErrors.invalid(using lib)(proof)(
                  tacticName = "QuantifiersIntro",
                  summary = "the changed formula on the left-hand side is not quantified",
                  factStatement = fact.statement,
                  bot = bot,
                  "Variables requested" -> vars.mkString(", "),
                  "Changed side" -> "left",
                  "Changed formula" -> changedFormula.toString,
                  "Diff" -> diff.toString
                )
          )

        case Sequent(_, s) if s.size == 1 =>
          val diffRest = bot.right -- s
          val changedFormula = s.head

          foldQuantifiers(
            (fact.statement.right -- diffRest).head,
            newFormula => bot.left |- diffRest + newFormula,
            "right",
            changedFormula match
              case ∀(_, _) => ((v, phi) => ∀(v, phi), RightForall)
              case ∃(_, _) => ((v, phi) => ∃(v, phi), RightExists)
              case _ =>
                return TacticErrors.invalid(using lib)(proof)(
                  tacticName = "QuantifiersIntro",
                  summary = "the changed formula on the right-hand side is not quantified",
                  factStatement = fact.statement,
                  bot = bot,
                  "Variables requested" -> vars.mkString(", "),
                  "Changed side" -> "right",
                  "Changed formula" -> changedFormula.toString,
                  "Diff" -> diff.toString
                )
          )

        case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty =>
          restateDirectly("the target sequent is identical to the source sequent, so the tactic expected a direct restatement")
        case _ =>
          return TacticErrors.invalid(using lib)(proof)(
            tacticName = "QuantifiersIntro",
            summary = "expected exactly one changed formula between the source and target sequents",
            factStatement = fact.statement,
            bot = bot,
            "Variables requested" -> vars.mkString(", "),
            "Diff" -> diff.toString
          )

  }

}
