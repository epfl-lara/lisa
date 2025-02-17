package lisa.maths
import lisa.automation.atp.*
import lisa.utils.KernelHelpers.checkProof
import lisa.utils.tptp.*


object Tests extends lisa.Main {
  draft()

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val rule8 = Axiom(forall(x, x === f(f(f(x)))) )
  val rule5 = Axiom(forall(x, forall(y, x === f(f(x)))) )

  val saturation = Theorem(∅ === f(∅)):
    have(thesis) by Egg.from(rule8, rule5)

    
  val exampleThm = Theorem( forall(x, P(x) ==> P(f(x))) |- P(∅) ==> P(f(f(∅))) ):
      val a = assume(forall(x, P(x) ==> P(f(x))))
      have(thesis) by Tautology.from(a of ∅, a of f(∅))
  
  val a, b, c = variable[Prop]

}
