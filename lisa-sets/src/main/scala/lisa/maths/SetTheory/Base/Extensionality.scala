package lisa.maths.SetTheory.Base

import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.SimpleDeducedSteps.*
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.automation.Tautology

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.{*, given}
import lisa.utils.fol.FOL.{*, given}

/**
  * Given the equivalence `z ∈ x <=> z ∈ y`, proves that `x = y` if `z` is free.
  *
  * {{{
  *  Γ ⊢ z ∈ x <=> z ∈ y, Δ
  * ------------------------
  *      Γ ⊢ x === y, Δ
  * }}}
  * where `z` is not free in `Γ` or `Δ`.
  */
def Extensionality(using proof: SetTheoryLibrary.Proof)(premise: proof.Fact)(conclusion: Sequent): proof.ProofTacticJudgement = {
  val x, y = variable[Ind]

  val premiseSeq = premise.statement
  val boundVars = premiseSeq.left.flatMap(_.freeVars)

  inline def valid(z1: Variable[Ind], z2: Variable[Ind], x: Expr[Ind], y: Expr[Ind]) =
    z1 == z2 && !boundVars.contains(z1) && conclusion.right.exists(isSame(_, x === y))

  val pivot: Option[(Variable[Ind], Expr[Ind], Expr[Ind])] = premiseSeq.right.collectFirst {
    case ((z: Variable[Ind]) ∈ x) <=> ((z_ : Variable[Ind]) ∈ y) if valid(z, z_, x, y) => (z, x, y)
  }

  pivot match {
    case None =>
      proof.InvalidProofTactic("Could not find a formula of the form z ∈ x <=> z ∈ y in the RHS of the premise.")
    case Some((z, x_, y_)) =>
      TacticSubproof {
        val equiv = z ∈ x_ <=> z ∈ y_
        val eq = x_ === y_
        val baseSequent = premiseSeq ->> equiv

        have(baseSequent +>> ∀(z, equiv)) by RightForall.withParameters(equiv, z)(premise)
        thenHave(baseSequent +>> eq) by Tautology.fromLastStep(extensionalityAxiom of (x := x_, y := y_))
      }
  }
}
