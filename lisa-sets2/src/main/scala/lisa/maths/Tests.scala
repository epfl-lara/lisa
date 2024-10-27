package lisa.maths
import lisa.automation.atp.Goeland

object Tests extends lisa.Main {
  draft()

  val x = variable[Term]
  val y = variable[Term]
  val z = variable[Term]
  val P = variable[Term >>: Formula]
  

  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Goeland // ("goeland/Example.buveurs2_sol")
  }
}