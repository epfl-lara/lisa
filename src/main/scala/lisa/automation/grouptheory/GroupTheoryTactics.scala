package lisa.automation.grouptheory

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.mathematics.SetTheory
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.{*, given}
import lisa.prooflib.*
import lisa.settheory.SetTheoryLibrary
import lisa.utils.KernelHelpers.*

object GroupTheoryTactics {
  import lisa.settheory.SetTheoryLibrary.{_, given}


  /**
   * <pre>
   * Γ |- ∃x. φ, Δ   Γ', φ, φ[y/x] |- x = y, Δ'
   * -------------------------------------------
   * Γ, Γ' |- ∃!x. φ, Δ, Δ'
   * </pre>
   *
   * This tactic separates the existence and the uniqueness proofs, which are often easier to prove independently,
   * and thus is easier to use than [[RightExistsOne]].
   */
  object ExistenceAndUniqueness extends ProofTactic {
    def withParameters(using proof: SetTheoryLibrary.Proof, om: OutputManager)(phi: Formula, x: VariableLabel, y: VariableLabel)
                      (existence: proof.Fact, uniqueness: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val existenceSeq = proof.getSequent(existence)
      val uniquenessSeq = proof.getSequent(uniqueness)

      lazy val substPhi = substituteVariables(phi, Map[VariableLabel, Term](x -> y))
      lazy val existenceFormula = ∃(x, phi)
      lazy val uniqueExistenceFormula = ∃!(x, phi)

      // Checking that all formulas are present
      if (x == y) {
        proof.InvalidProofTactic("x and y can not be equal.")
      } else if (!contains(existenceSeq.right, existenceFormula)) {
        proof.InvalidProofTactic(s"Existence sequent conclusion does not contain ∃$x. φ.")
      } else if (!contains(uniquenessSeq.left, phi)) {
        proof.InvalidProofTactic("Uniqueness sequent premises do not contain φ.")
      } else if (!contains(uniquenessSeq.left, substPhi)) {
        proof.InvalidProofTactic(s"Uniqueness sequent premises do not contain φ[$y/$x].")
      } else if (!contains(uniquenessSeq.right, x === y) && !contains(uniquenessSeq.right, y === x)) {
        proof.InvalidProofTactic(s"Uniqueness sequent premises do not contain $x = $y")
      } else if (!contains(bot.right, uniqueExistenceFormula)) {
        proof.InvalidProofTactic(s"Bottom sequent conclusion does not contain ∃!$x. φ")
      }

      // Checking pivots
      else if (!isSameSet(existenceSeq.left ++ uniquenessSeq.left, bot.left + phi + substPhi)) {
        proof.InvalidProofTactic("Could not infer correct left pivots.")
      } else if (!isSameSet(existenceSeq.right ++ uniquenessSeq.right + uniqueExistenceFormula, bot.right + existenceFormula + (x === y))) {
        proof.InvalidProofTactic("Could not infer correct right pivots.")
      } else {
        val gammaPrime = uniquenessSeq.left.filter(f => !isSame(f, phi) && !isSame(f, substPhi))
        
        val steps = SUBPROOF(using proof)(Some(bot)) {
          val forward = have(phi |- ((x === y) ==> substPhi)) subproof {
            assume(phi)
            thenHave((x === y) |- substPhi) by Substitution
            thenHave((x === y) ==> substPhi) by Restate
          }

          for (f <- gammaPrime) {
            assume(f)
          }
          
          val backward = have(phi |- (substPhi ==> (x === y))) by Restate.from(uniqueness)

          have(phi |- ((x === y) <=> substPhi))
          have(phi |- ((x === y) <=> substPhi)) by RightIff(forward, backward)
          thenHave(phi |- ∀(y, (x === y) <=> substPhi)) by RightForall
          thenHave(phi |- ∃(x, ∀(y, (x === y) <=> substPhi))) by RightExists
          thenHave(∃(x, phi) |- ∃(x, ∀(y, (x === y) <=> substPhi))) by LeftExists
          val cut = thenHave(∃(x, phi) |- ∃!(x, phi)) by RightExistsOne

          have(bot) by Cut(existence, cut)
        }

        unwrapTactic(steps.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof for ExistenceAndUniqueness failed.")
      }
    }

    def apply(using proof: SetTheoryLibrary.Proof, om: OutputManager)(phi: Formula)(existence: proof.Fact, uniqueness: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val existenceSeq = proof.getSequent(existence)
      val uniquenessSeq = proof.getSequent(uniqueness)

      if (!contains(uniquenessSeq.left, phi)) {
        return proof.InvalidProofTactic("Uniqueness sequent premises do not contain φ.")
      }

      // Try to infer x and y from the uniqueness sequent right-hand side equality
      uniquenessSeq.right.collect {
        case PredicateFormula(`equality`, List(Term(x: VariableLabel, _), Term(y: VariableLabel, _))) if x != y => (x, y)
      }.collectFirst {
        case (x, y) if contains(uniquenessSeq.left, substituteVariables(phi, Map[VariableLabel, Term](x -> y))) =>
          ExistenceAndUniqueness.withParameters(phi, x, y)(existence, uniqueness)(bot)
        case (x, y) if contains(uniquenessSeq.left, substituteVariables(phi, Map[VariableLabel, Term](y -> x))) =>
          ExistenceAndUniqueness.withParameters(phi, y, x)(existence, uniqueness)(bot)
      }.getOrElse(proof.InvalidProofTactic("Could not infer correct variables in uniqueness sequent."))
    }
  }
}
