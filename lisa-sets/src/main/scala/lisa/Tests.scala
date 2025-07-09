package lisa.maths
import lisa.automation.atp.*
import lisa.utils.KernelHelpers.checkProof
import lisa.tptp.*
import lisa.utils.KernelHelpers.flattenProof

object Tests extends lisa.Main {
  draft()
  //withCache()

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]
  val P = variable[Ind >>: Prop]
  val d = variable[Ind >>: Prop]
  val Q = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val t0 = constant[Ind]
  val t1 = constant[Ind]
  val t2 = constant[Ind]
  val t3 = constant[Ind]
  val a = constant[Ind]
  val mult = variable[Ind >>: Ind >>: Ind]
  val div = variable[Ind >>: Ind >>: Ind]
  addSymbol(t0)
  addSymbol(t1)
  addSymbol(t2)
  addSymbol(t3)
  addSymbol(a)

  extension (t: Expr[Ind]) {
    def /(y: Expr[Ind]): Expr[Ind] = div(t)(y)
    def *(y: Expr[Ind]): Expr[Ind] = mult(t)(y)
  }

  def _div(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = div(x)(y)
  def _mult(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = mult(x)(y)

  val divide_mult_shift = Theorem(
    (
      ∀(x, x / t1 === x),
      ∀(x, ∀(y, x / y === t1 / (y / x))),
      ∀(x, ∀(y, (x / y) * y === x))
    ) |- ((t2 / t3) * (t3 / t2)) / t1 === t1
  ):
    have(thesis) by Egg

  val saturation = Theorem((∀(x, x === f(f(f(x)))), ∀(x, ∀(y, x === f(f(x))))) |- a === f(a)):
    have(thesis) by Egg

  val drinkers2 = Theorem(∃(x, ∀(y, d(x) ==> d(y)))):
    have(thesis) by Goeland

  val example = Theorem((∀(x, P(x)) \/ ∀(y, Q(y))) ==> (P(a) \/ Q(a))):
    have(thesis) by Prover9



  val example2 = Theorem(∃(x, ∀(y, d(x) ==> d(y)))):
    have(thesis) by Prover9


  val dr2proof = flattenProof(drinkers2.kernelProof.get)
  java.lang.Thread.sleep(5)
  checkProof(dr2proof)
  java.lang.Thread.sleep(5)
  val tptpproof = ProofPrinter.proofToTPTP(dr2proof, Map(), ("drinkers2", drinkers2.statement.underlying), false)
  tptpproof.foreach { p => println(p.pretty)}


}
