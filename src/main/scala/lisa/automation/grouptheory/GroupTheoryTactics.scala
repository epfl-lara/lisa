package lisa.automation.grouptheory

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.mathematics.SetTheory
import lisa.prooflib.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.{*, given}
import lisa.settheory.SetTheoryLibrary
import lisa.utils.KernelHelpers.*

object GroupTheoryTactics {
  import lisa.settheory.SetTheoryLibrary.{*, given}


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

    def apply(using proof: SetTheoryLibrary.Proof, om: OutputManager)(phi: Formula)(existence: proof.Fact, uniqueness: proof.Fact)
             (bot: Sequent): proof.ProofTacticJudgement = {
      val existenceSeq = proof.getSequent(existence)
      val uniquenessSeq = proof.getSequent(uniqueness)

      // Try to infer x from the premises
      // Specifically, find variables in the correct quantifiers, common to all three sequents
      val existsVars = existenceSeq.right.collect {
        case BinderFormula(Exists, x, f) if isSame(f, phi) => x
      }
      if (existsVars.isEmpty) {
        return proof.InvalidProofTactic("Missing existential quantifier in the existence sequent.")
      }

      val commonVars = bot.right.collect {
        case BinderFormula(ExistsOne, x, f) if isSame(f, phi) && existsVars.contains(x) => x
      }
      if (commonVars.isEmpty || commonVars.size > 1) {
        return proof.InvalidProofTactic("Could not infer correct variable x in quantifiers.")
      }

      val x = commonVars.head

      // Infer y from the equalities in the uniqueness sequent
      uniquenessSeq.right.collectFirst {
        case PredicateFormula(`equality`, List(Term(`x`, _), Term(y: VariableLabel, _)))
          if x != y && contains(uniquenessSeq.left, substituteVariables(phi, Map[VariableLabel, Term](x -> y))) => y

        case PredicateFormula(`equality`, List(Term(y: VariableLabel, _), Term(`x`, _)))
          if x != y && contains(uniquenessSeq.left, substituteVariables(phi, Map[VariableLabel, Term](x -> y))) => y
      } match {
        case Some(y) => ExistenceAndUniqueness.withParameters(phi, x, y)(existence, uniqueness)(bot)
        case None => proof.InvalidProofTactic("Could not infer correct variable y in uniqueness sequent.")
      }
    }
  }

  /** 
   * <pre>
   * Γ, φ |- Δ, Σ   Γ, ¬φ |- Δ, Σ'  
   * -----------------------------
   * Γ |- Δ
   * </pre>
   *
   *
   * TODO: Extending the tactic to more general pivots
   */
  object Cases extends ProofTactic {
    def withParameters(using proof: SetTheoryLibrary.Proof, om: OutputManager)(phi: Formula)(pos: proof.Fact, neg: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val seqPos = proof.getSequent(pos)
      val seqNeg = proof.getSequent(neg)

      if (!(contains(seqPos.left, phi)  && contains(seqNeg.left, !phi) && !contains(seqNeg.left, phi)) &&
          !(contains(seqPos.left, !phi) && contains(seqNeg.left, phi) && !contains(seqNeg.left, !phi))) {
        proof.InvalidProofTactic("The given sequent do not contain φ or ¬φ.")
      } else {
        val gamma = bot.left
        val steps = SUBPROOF(using proof)(Some(bot)) {
          val excludedMiddle = have(phi \/ !phi) by Tautology
          val toCut = have((gamma + (phi \/ !phi)) |- bot.right) by LeftOr(pos, neg)

          have(thesis) by Cut(excludedMiddle, toCut)
        }

        unwrapTactic(steps.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof for Cases failed.")
      }
    }

    def apply(using proof: SetTheoryLibrary.Proof, om: OutputManager)(pos: proof.Fact, neg: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val seqPos = proof.getSequent(pos)
      val pivot = seqPos.left -- bot.left

      if (pivot.size != 1) {
        proof.InvalidProofTactic("Could not infer correct formula φ.")
      } else {
        Cases.withParameters(pivot.head)(pos, neg)(bot)
      }
    }
  }
}
