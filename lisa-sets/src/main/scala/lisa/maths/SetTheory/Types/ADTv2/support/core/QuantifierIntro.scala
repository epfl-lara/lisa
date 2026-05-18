package lisa.maths.SetTheory.Types.ADTv2.support.core

import lisa.maths.SetTheory.SetTheory.{*, given}

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*

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
      proof: lib.Proof
  )(
      vars: Seq[Variable[Ind]]
  )(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof { sp ?=>
    if vars.isEmpty then lib.have(bot) by Restate.from(fact)
    else
      val diff: Sequent = bot -- fact.statement

      diff match
        case Sequent(s, _) if s.size == 1 =>
          val diffRest = bot.left -- s
          val f = s.head
          val fWithoutQuant = (fact.statement.left -- diffRest).head
          f match
            case ∀(_, _) => vars
                .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                  val (accFact, accFormula) = acc
                  val newFormula = ∀(v, accFormula)
                  (
                    lib.have(diffRest + newFormula |- bot.right) by LeftForall(accFact),
                    newFormula
                  )
                }
            case ∃(_, _) => vars
                .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                  val (accFact, accFormula) = acc
                  val newFormula = ∃(v, accFormula)
                  (
                    lib.have(diffRest + newFormula |- bot.right) by LeftExists(accFact),
                    newFormula
                  )
                }
            case _ => return proof
                .InvalidProofTactic(s"The formula that changed is not quantified: $f.")
        case Sequent(_, s) if s.size == 1 =>
          val diffRest = bot.right -- s
          val f = s.head
          val fWithoutQuant = (fact.statement.right -- diffRest).head
          f match
            case ∀(_, _) => vars
                .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                  val (accFact, accFormula) = acc
                  val newFormula = forall(v, accFormula)
                  (
                    lib.have(bot.left |- diffRest + newFormula) by RightForall(accFact),
                    newFormula
                  )
                }
            case ∃(_, _) => vars
                .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                  val (accFact, accFormula) = acc
                  val newFormula = exists(v, accFormula)
                  (
                    lib.have(bot.left |- diffRest + newFormula) by RightExists(accFact),
                    newFormula
                  )
                }
            case _ => return proof
                .InvalidProofTactic(s"The formula that changed is not quantified: $f.")
        case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty =>
          lib.have(bot) by Restate.from(fact)
        case _ => return proof
            .InvalidProofTactic("Two or more formulas in the sequent have changed.")

  }

}
