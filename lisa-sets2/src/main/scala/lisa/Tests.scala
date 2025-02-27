
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


  def _div(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = div(x)(y)
  def _mult(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = mult(x)(y)

  val divide_mult_shift = Theorem((
    forall(x, _div(x, t1) === x),
    forall(x, forall(y, _div(x, y) === _div(t1, _div(y, x)))),
    //forall(x, forall(y, forall(z, _div(x, _div(y, z)) === _div(_mult(x, z), _mult(_div(y, z), z))))),
    forall(x, forall(y, _mult(_div(x, y), y) === x)),
    //forall(x, _mult(x, t1) === x)
  ) |- _div(_mult(_div(t2, t3), _div(t3, t2)), t1) === t1):
    have(thesis) by Egg

    /*
  val saturation = Theorem(
    (forall(x, x === f(f(f(x)))), forall(x, forall(y, x === f(f(x))))) |- ∅ === f(∅)):
    have(thesis) by Egg
*/
    /*
  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))):
    have(thesis) by Goeland

  val example = Theorem( (forall(x, P(x)) \/ forall(y, Q(y))) ==> (P(∅) \/ Q(∅)) ):
    have(thesis) by Prover9
  */

}
