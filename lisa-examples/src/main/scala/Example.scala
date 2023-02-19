import lisa.Main
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.FOLPrinter.*
import lisa.utils.KernelHelpers.{*, given}

/**
 * Discover some of the elements of LISA to get started.
 */
object Example {

  import lisa.kernel.proof.SequentCalculus.*
  val phi = formulaVariable()
  val psi = formulaVariable()
  val PierceLaw = SCProof(
    Hypothesis(phi |- phi, phi),
    Weakening(phi |- (phi, psi), 0),
    RightImplies(() |- (phi, phi ==> psi), 1, phi, psi),
    LeftImplies((phi ==> psi) ==> phi |- phi, 2, 0, (phi ==> psi), phi),
    RightImplies(() |-((phi ==> psi) ==> phi) ==> phi, 3, (phi ==> psi) ==> phi, phi)
  )
  def main(args: Array[String]): Unit = {
    checkProof(PierceLaw)
  }

}

object Example2 extends lisa.Main {

  val x = variable
  val P = predicate(1)
  val f = function(1)
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    assume(∀(x, P(x) ==> P(f(x))))
    assume(P(x))
    val step1 = have(P(x) ==> P(f(x))) by InstantiateForall
    val step2 = have(P(f(x)) ==> P(f(f(x)))) by InstantiateForall
    have(thesis) by Tautology.from(step1, step2)
  }
  show

}
