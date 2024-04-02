package lisa.maths.settheory.types

import lisa.fol.FOL.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.unification.UnificationUtils.*
import scala.util.boundary, boundary.break

object QuantifiersIntro extends ProofTactic {
  def apply(using lib: Library, proof: lib.Proof)(vars: Seq[Variable], rightToLeft: Boolean = true)(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
    TacticSubproof { sp ?=>
      if vars.isEmpty then
        lib.have(bot) by Restate.from(fact)
      else
        val diff: Sequent = bot -- fact.statement

        diff match
          case Sequent(s, _) if s.size == 1 =>
            val diffRest = bot.left -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.left -- diffRest).head
            f match
              case BinderFormula(Forall, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = forall(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = exists(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftExists(accFact), newFormula)
                )
              case _ => return proof.InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(_, s) if s.size == 1 =>
            val diffRest = bot.right -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.right -- diffRest).head
            f match
              case BinderFormula(Forall, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = forall(v, accFormula)
                  (lib.have(bot.left |- diffRest + newFormula) by RightForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = exists(v, accFormula)
                  (lib.have(bot.left |- diffRest + newFormula) by RightExists(accFact), newFormula)
                )
              case _ => return proof.InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty => lib.have(bot) by Restate.from(fact)
          case _ => return proof.InvalidProofTactic("Two or more formulas in the sequent have changed.")


    }  
}