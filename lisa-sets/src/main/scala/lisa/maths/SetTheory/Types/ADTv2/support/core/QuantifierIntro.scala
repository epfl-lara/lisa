package lisa.maths.SetTheory.Types.ADTv2.support.core

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.{
  UnapplicableProofTactic,
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

    def foldQuantifiers(
      fWithoutQuant: Expr[Prop],
      mkBot: Expr[Prop] => Sequent,
      mkFormulaAndTactic: ((Variable[Ind], Expr[Prop]) => Expr[Prop], ProofFactSequentTactic & ProofTactic),
    ): (sp.Fact, Expr[Prop]) =
      vars.foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
        val (mkFormula, tactic) = mkFormulaAndTactic
        val (accFact, accFormula) = acc
        val newFormula = mkFormula(v, accFormula)
        try (lib.have(mkBot(newFormula)) by tactic(accFact), newFormula)
        catch
          case e: UnapplicableProofTactic =>
            throw UnapplicableProofTactic(
              this,
              proof,
              s"""${tactic.name} on $v failed in QuantifiersIntro.
                |Current formula: $accFormula
                |Target formula: $newFormula
                |Underlying error: ${e.getMessage}""".stripMargin
            )
      }

    if vars.isEmpty then lib.have(bot) by Restate.from(fact)
    else
      val diff: Sequent = bot -- fact.statement

      diff match
        case Sequent(s, _) if s.size == 1 =>
          val diffRest = bot.left -- s

          foldQuantifiers(
            (fact.statement.left -- diffRest).head,
            newFormula => diffRest + newFormula |- bot.right,
            s.head match
              case ∀(_, _) => ((v, phi) => ∀(v, phi), LeftForall)
              case ∃(_, _) => ((v, phi) => ∃(v, phi), LeftExists)
              case _ => return proof
                  .InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          )

        case Sequent(_, s) if s.size == 1 =>
          val diffRest = bot.right -- s

          foldQuantifiers(
            (fact.statement.right -- diffRest).head,
            newFormula => bot.left |- diffRest + newFormula,
            s.head match
              case ∀(_, _) => ((v, phi) => ∀(v, phi), RightForall)
              case ∃(_, _) => ((v, phi) => ∃(v, phi), RightExists)
              case _ => return proof
                  .InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          )

        case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty =>
          lib.have(bot) by Restate.from(fact)
        case _ => return proof
            .InvalidProofTactic("Two or more formulas in the sequent have changed.")

  }

}
