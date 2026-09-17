package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.BasicStepTactic.{LeftExists, LeftForall, Restate, RightExists, RightForall, TacticSubproof, Weakening}
import lisa.utils.prooflib.ProofTacticLib.{ProofFactSequentTactic, ProofTactic}
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

import scala.util.boundary
import scala.util.boundary.break

object InstantiateForallSeq extends ProofTactic {

  /**
   * Repeatedly instantiates the right-hand side of a fact through a sequence of
   * universal quantifiers.
   *
   * Typical use:
   *   from `forallSeq(vars, phi(vars))`
   *   derive `phi(args)`.
   */
  def apply(using
      lib: Library,
      proof: lib.Proof
  )(
      args: Seq[Expr[Ind]]
  )(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = boundary:
    TacticSubproof { sp ?=>
      val initialCurrent = TacticErrors.attemptOrInvalid(using lib)(proof)(
        tacticName = "InstantiateForallSeq",
        summary = "failed before any instantiation while importing the original fact",
        factStatement = fact.statement,
        bot = bot,
        "Arguments requested" -> args.mkString(", ")
      ) {
        lib.have(fact.statement) by Restate.from(fact)
      } match
        case Left(judgement) => break(judgement)
        case Right(value)    => value

      var current = initialCurrent

      for (arg, index) <- args.zipWithIndex do
        current.statement.right.head match
          case forall(v, phi) =>
            current = TacticErrors.attemptOrInvalid(using lib)(proof)(
              tacticName = "InstantiateForallSeq",
              summary = s"failed while instantiating argument #${index + 1} with `$arg`",
              factStatement = fact.statement,
              bot = bot,
              "Arguments requested" -> args.mkString(", "),
              "Current intermediate statement" -> current.statement.toString,
              "Current quantified variable" -> v.toString
            ) {
              lib.have(phi.substitute(v := arg).asInstanceOf[Expr[Prop]]) by InstantiateForall(arg)(current)
            } match
              case Left(judgement) => break(judgement)
              case Right(value)    => value
          case _ =>
            break(TacticErrors.invalid(using lib)(proof)(
              tacticName = "InstantiateForallSeq",
              summary = s"expected a universally quantified formula while instantiating argument #${index + 1}",
              factStatement = fact.statement,
              bot = bot,
              "Argument" -> arg.toString,
              "Arguments requested" -> args.mkString(", "),
              "Current intermediate statement" -> current.statement.toString,
              "Current right-hand formula" -> current.statement.right.head.toString
            ))

      TacticErrors.attemptOrInvalid(using lib)(proof)(
        tacticName = "InstantiateForallSeq",
        summary = "failed while closing the instantiated theorem",
        factStatement = fact.statement,
        bot = bot,
        "Arguments requested" -> args.mkString(", "),
        "Current intermediate statement" -> current.statement.toString
      ) {
        lib.have(bot) by Weakening(current)
      } match
        case Left(judgement) => break(judgement)
        case Right(_)        => ()
  }
}

object QuantifiersIntro extends ProofTactic {

  /**
   * Executes the tactic on a specific goal.
   */
  def apply(using
      lib: Library,
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
