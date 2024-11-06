package lisa.maths
import lisa.automation.atp.*
import lisa.utils.KernelHelpers.checkProof
import lisa.utils.tptp.*


object Tests extends lisa.Main {
  draft()

  val x = variable[Term]
  val y = variable[Term]
  val z = variable[Term]
  val P = variable[Term >>: Formula]
  val f = variable[Term >>: Term]

  val rule8 = Axiom(forall(x, x === f(f(f(f(f(f(f(f(x))))))))) )
  val rule5 = Axiom(forall(x, x === f(f(f(f(f(x)))))) )

  val saturation = Theorem(∅ === f(∅)):
    have(thesis) by Egg.from(rule8, rule5)

}
