
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

  val rule8 = Axiom(forall(x, x === f(f(f(x)))) )
  val rule5 = Axiom(forall(x, forall(y, x === f(f(x)))) )

  val saturation = Theorem(∅ === f(∅)):
    have(thesis) by Egg.from(rule8, rule5)

    
  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))):
      have(thesis) by Goeland


  val example = Theorem( (forall(x, P(x)) \/ forall(y, Q(y))) ==> (P(∅) \/ Q(∅)) ):
    have(thesis) by Prover9
  

}
