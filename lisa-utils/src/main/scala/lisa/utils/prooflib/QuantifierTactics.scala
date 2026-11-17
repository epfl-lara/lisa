package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.LeftForall
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightExists
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.BasicStepTactic.TacticSubproof
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.ProofTacticLib.ProofFactSequentTactic
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
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
    if fact.statement.right.size != 1 then break(proof.InvalidProofTactic("InstantiateForallSeq requires exactly one formula on the right of its input fact."))
    TacticSubproof { sp ?=>
      val initialCurrent = TacticErrors.attemptOrInvalid(using lib)(proof)(
        tacticName = "InstantiateForallSeq",
        summary = "failed before any instantiation while importing the original fact",
        factStatement = fact.statement,
        bot = bot,
        entries = Seq("Arguments requested" -> args.mkString(", "))
      ) {
        lib.have(fact.statement) by Weakening(fact)
      } match
        case Left(judgement) => break(judgement)
        case Right(value) => value

      var current = initialCurrent

      for (arg, index) <- args.zipWithIndex do
        current.statement.right.head match
          case forall(v, phi) =>
            current = TacticErrors.attemptOrInvalid(using lib)(proof)(
              tacticName = "InstantiateForallSeq",
              summary = s"failed while instantiating argument #${index + 1} with `$arg`",
              factStatement = fact.statement,
              bot = bot,
              entries = Seq(
                "Arguments requested" -> args.mkString(", "),
                "Current intermediate statement" -> current.statement.toString,
                "Current quantified variable" -> v.toString
              )
            ) {
              lib.have(current.statement.left |- phi.substitute(v := arg)) by InstantiateForall(arg)(current)
            } match
              case Left(judgement) => break(judgement)
              case Right(value) => value
          case _ =>
            break(
              TacticErrors.invalid(using lib)(proof)(
                tacticName = "InstantiateForallSeq",
                summary = s"expected a universally quantified formula while instantiating argument #${index + 1}",
                factStatement = fact.statement,
                bot = bot,
                "Argument" -> arg.toString,
                "Arguments requested" -> args.mkString(", "),
                "Current intermediate statement" -> current.statement.toString,
                "Current right-hand formula" -> current.statement.right.head.toString
              )
            )

      TacticErrors.attemptOrInvalid(using lib)(proof)(
        tacticName = "InstantiateForallSeq",
        summary = "failed while closing the instantiated theorem",
        factStatement = fact.statement,
        bot = bot,
        entries = Seq(
          "Arguments requested" -> args.mkString(", "),
          "Current intermediate statement" -> current.statement.toString
        )
      ) {
        lib.have(bot) by Weakening(current)
      } match
        case Left(judgement) => break(judgement)
        case Right(_) => ()
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
        entries = Seq("Variables requested" -> vars.mkString(", "))
      ) {
        lib.have(bot) by Restate.from(fact)
      } match
        case Left(judgement) => judgement
        case Right(value) => value

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
            entries = Seq(
              "Variables requested" -> vars.mkString(", "),
              "Side" -> side,
              "Current formula" -> accFormula.toString,
              "Target formula" -> newFormula.toString
            )
          ) {
            lib.have(mkBot(newFormula)) by tactic(accFact)
          },
          newFormula
        )
      }

    if vars.isEmpty then restateDirectly("no variables were requested, so the tactic expected a direct restatement")
    else
      val diff: Sequent = bot -- fact.statement
      val sourceDiff: Sequent = fact.statement -- bot

      diff match
        case Sequent(s, t) if s.size == 1 && t.isEmpty && sourceDiff.left.size == 1 && sourceDiff.right.isEmpty =>
          val diffRest = bot.left -- s
          val changedFormula = s.head

          foldQuantifiers(
            sourceDiff.left.head,
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

        case Sequent(t, s) if s.size == 1 && t.isEmpty && sourceDiff.right.size == 1 && sourceDiff.left.isEmpty =>
          val diffRest = bot.right -- s
          val changedFormula = s.head

          foldQuantifiers(
            sourceDiff.right.head,
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

        case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty && sourceDiff.left.isEmpty && sourceDiff.right.isEmpty =>
          restateDirectly("the target sequent is identical to the source sequent, so the tactic expected a direct restatement")
        case _ =>
          return TacticErrors.invalid(using lib)(proof)(
            tacticName = "QuantifiersIntro",
            summary = "expected exactly one source formula to be replaced by a quantified formula on the same side",
            factStatement = fact.statement,
            bot = bot,
            "Variables requested" -> vars.mkString(", "),
            "Added formulas" -> diff.toString,
            "Removed formulas" -> sourceDiff.toString
          )

  }
}
