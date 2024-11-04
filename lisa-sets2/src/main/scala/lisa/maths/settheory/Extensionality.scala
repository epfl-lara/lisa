package lisa.maths.settheory

import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.Library
import lisa.SetTheoryLibrary
import lisa.prooflib.ProofTacticLib.ProofFactSequentTactic

object Extensionality extends lisa.Main:

  private val s = variable[Term]
  private val x = variable[Term]
  private val y = variable[Term]
  private val z = variable[Term]
  private val P = variable[Term >>: Formula]
  private val Q = variable[Term >>: Term >>: Formula]

  val implied = Theorem( forall(z, z ∈ x <=> z ∈ y) |- (x === y) ):
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
    inline def valid(z1: Variable[T], z2: Variable[T], x: Expr[T], y: Expr[T]) =
      z1 == z2 && !boundVars.contains(z1) && conclusion.right.exists(isSame(_, x === y))
    val pivot: Option[(Variable[T], Expr[T], Expr[T])] = premise.right.collectFirst:
      case (<=> #@ (∈ #@ (z1: Variable[T]) #@ (x: Expr[T])) #@ (∈ #@ (z2: Variable[T]) #@ (y: Expr[T]))) if valid(z1, z2, x, y) => (z1, x, y)

    pivot match
      case None => 
        proof.InvalidProofTactic("Could not find a formula of the form z ∈ x <=> z ∈ y in the RHS of the premise.")
      case Some((z, xe, ye)) =>
        TacticSubproof:
          val pivot = z ∈ xe <=> z ∈ ye
          val qpivot = forall(z, pivot)
          val eq = xe === ye
          val implication = 
            proof.InstantiatedFact(implied, Seq(x := xe, y := ye))

          have(premise ->> pivot +>> qpivot) by RightForall.withParameters(pivot, z)(premiseStep)
          have(premise ->> pivot +>> eq) by Cut.withParameters(qpivot)(lastStep, implication)

end Extensionality