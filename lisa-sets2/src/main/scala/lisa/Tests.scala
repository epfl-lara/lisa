
package lisa.maths
import lisa.automation.atp.*
import lisa.utils.KernelHelpers.checkProof
import lisa.tptp.*


object Tests extends lisa.Main {
  draft()

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]
  val P = variable[Ind >>: Prop]
  val Q = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val saturation = Theorem(
    (forall(x, x === f(f(f(x)))), forall(x, forall(y, x === f(f(x))))) |- ∅ === f(∅)):
    have(thesis) by Egg

    /*
  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))):
    have(thesis) by Goeland

  val example = Theorem( (forall(x, P(x)) \/ forall(y, Q(y))) ==> (P(∅) \/ Q(∅)) ):
    have(thesis) by Prover9
  */

}
