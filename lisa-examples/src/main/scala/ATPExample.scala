
import lisa.automation.atp.Egg
import lisa.automation.atp.Goeland

/**
 * Example showing discharge of proofs using egg and the Goeland theorem prover.
 * Will fail if Goeland is not available on PATH.
 */
object ATPExample extends lisa.Main:
  draft()
  
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  // val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))):
  //   have(thesis) by Goeland

  val rule8 = Axiom(forall(x, x === f(f(f(f(f(f(f(f(x))))))))))
  val rule5 = Axiom(forall(x, x === f(f(f(f(f(x)))))))

  val saturation = Theorem(∅ === f(∅)):
    have(thesis) by Egg.from(rule8, rule5)