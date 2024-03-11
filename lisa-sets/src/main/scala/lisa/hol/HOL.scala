package lisa

import lisa.SetTheoryLibrary
import lisa.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait HOL extends BasicMain {
  export lisa.maths.settheory.types.TypeSystem.{`*` => _, *}
  export lisa.maths.settheory.types.TypeLib.{any, Zero, One, 𝔹, |=>, |-}
  export TypeChecker.*
  export lisa.hol.VarsAndFunctions.{main => _, given, *}
  export SetTheoryLibrary.{*, given}
  val STL = SetTheoryLibrary
  val F: lisa.fol.FOL.type = lisa.fol.FOL
  export F.{Term, variable, ===, given}



  private val A = variable


  def assume(using proof: library.Proof)(t: Term): proof.ProofStep =
    proof.addAssumption(eqOne(t))
    val seq = HOLSequent(Set(), t)
    val r = have(seq) by lisa.prooflib.BasicStepTactic.Hypothesis
    r


  def withCTX(s:F.Sequent): F.Sequent =
    val ctx = computeContextOfFormulas(s.left ++ s.right)
    s ++<< ((ctx._1 ++ ctx._2) |- ())
  

}