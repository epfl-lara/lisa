package lisa

import lisa.SetTheoryLibrary
import lisa.prooflib.BasicMain
import lisa.prooflib.OutputManager

/**
 * The parent trait of all theory files containing mathematical development
 */
trait _HOL extends BasicMain {
  export lisa.maths.settheory.types.TypeSystem.{`*` => _, *}
  export lisa.maths.settheory.types.TypeLib.{any, Zero, One, |=>, |-}
  export TypeChecker.*
  export lisa.hol.VarsAndFunctions.{main => _, given, *}
  export SetTheoryLibrary.{Theorem => _, *, given}
  val STL = SetTheoryLibrary
  val F: lisa.fol.FOL.type = lisa.fol.FOL
  export F.{Term, variable, ===, given}
  //export lisa.hol.HOLSteps.*



  def assume(using proof: library.Proof)(t: Term): proof.ProofStep =
    proof.addAssumption(eqOne(t))
    val seq = HOLSequent(Set(), t)
    val r = have(seq) by lisa.prooflib.BasicStepTactic.Hypothesis
    r


  def withCTX(s:F.Sequent): F.Sequent =
    val ctx = computeContextOfFormulas(s.left ++ s.right)
    s ++<< ((ctx._1 ++ ctx._2) |- ())
  

}

trait HOL extends _HOL {
  export lisa.hol.HOLSteps.*

  export lisa.prooflib.BasicStepTactic.*
  export lisa.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau
  export lisa.automation.Apply
  export lisa.automation.Exact

  def Theorem(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: F.Sequent)(computeProof: Proof ?=> Unit): THM = 
    val (l1, l2) = computeContext(statement.freeVariables.toSet)
    SetTheoryLibrary.Theorem(statement ++<< ((l1 ++ l2) |- ()))(computeProof)

}