package lisa.maths.settheory

import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.Library
import lisa.SetTheoryLibrary
import lisa.utils.prooflib.ProofTacticLib.ProofFactSequentTactic

object Extensionality extends lisa.Main:

  private val s = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Ind >>: Prop]

  val implied = Theorem(forall(z, z ∈ x <=> z ∈ y) |- (x === y)):
    have(thesis) by Weakening(extensionalityAxiom)

  /**
   * Given that z ∈ x <=> z ∈ y, prove that x = y if z is free.
   *
   *  Γ ⊢ z ∈ x <=> z ∈ y, Δ
   * ------------------------ z not in Γ
   *      Γ ⊢ x === y, Δ
   */
  def tactic(using proof: Proof)(premiseStep: proof.Fact)(conclusion: Sequent) =
    val premise = proof.getSequent(premiseStep)
    val boundVars = premise.left.flatMap(_.freeVars)
    inline def valid(z1: Variable[Ind], z2: Variable[Ind], x: Expr[Ind], y: Expr[Ind]) =
      z1 == z2 && !boundVars.contains(z1) && conclusion.right.exists(isSame(_, x === y))
    val pivot: Option[(Variable[Ind], Expr[Ind], Expr[Ind])] = premise.right.collectFirst:
      case (<=> #@ (∈ #@ (z1: Variable[Ind]) #@ (x: Expr[Ind])) #@ (∈ #@ (z2: Variable[Ind]) #@ (y: Expr[Ind]))) if valid(z1, z2, x, y) => (z1, x, y)

    pivot match
      case None =>
        proof.InvalidProofTactic("Could not find a formula of the form z ∈ x <=> z ∈ y in the RHS of the premise.")
      case Some((z, xe, ye)) =>
        TacticSubproof:
          val pivot = z ∈ xe <=> z ∈ ye
          val qpivot = forall(z, pivot)
          val eq = xe === ye
          val baseSequent = premise ->> pivot
          val implication = proof.InstantiatedFact(implied, Seq(x := xe, y := ye))

          have(baseSequent +>> qpivot) by RightForall.withParameters(pivot, z)(premiseStep)
          have(baseSequent +>> eq) by Cut.withParameters(qpivot)(lastStep, implication)

end Extensionality
