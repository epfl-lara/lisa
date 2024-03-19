package lisa.maths.settheory.types

import lisa.fol.FOL.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.unification.UnificationUtils.*
import scala.util.boundary, boundary.break


object OrAggregate extends ProofTactic {

  def apply(using lib: Library, proof: lib.Proof)(facts: Seq[proof.Fact])(bot: Sequent): proof.ProofTacticJudgement =

    TacticSubproof { sp ?=>
      if facts.isEmpty then
          lib.have(bot) by Restate
      else
        val left = facts.head.statement.left.filter(bot.left.contains)
        val right = bot.right

        val start = lib.have( left + False |- right) by Restate

        facts.foldLeft((start, False.asInstanceOf[Formula])) (
          (acc, fact) => 
            val (aggreg, tail) = acc

            val head = (fact.statement.left -- left).head

            (lib.have(left + (tail \/ head) |- right) by LeftOr(aggreg, fact), tail \/ head)
        )
    }  
}

object AndAggregate extends ProofTactic {

  def apply(using lib: Library, proof: lib.Proof)(facts: Seq[proof.Fact])(bot: Sequent): proof.ProofTacticJudgement =

    

    TacticSubproof { sp ?=>
      if facts.isEmpty then
        lib.have(bot) by Restate
      else
        val left = bot.left
        val start = lib.have( left |- True) by Restate

        facts.foldLeft((start, True.asInstanceOf[Formula])) (
          (acc, fact) => 
            val (aggreg, tail) = acc

            val head = fact.statement.right.head

            (lib.have(left |- tail /\ head) by RightAnd(aggreg, fact), tail /\ head)
        )
    }  
}
