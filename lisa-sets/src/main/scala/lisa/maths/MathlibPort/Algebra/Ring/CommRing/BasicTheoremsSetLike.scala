package lisa.maths.MathlibPort.Algebra.Ring.CommRing

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Basic projection theorems for [[Defs.commRing]].
 */
object BasicTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val commRing_isRing = Theorem(
    Defs.commRing(R)(add)(zero)(negOp)(mul)(one) |- RingDefs.ring(R)(add)(zero)(negOp)(mul)(one)
  ) {
    have(thesis) by Tautology.from(Defs.commRing.definition)
  }

  val commRing_mul_comm = Theorem(
    Defs.commRing(R)(add)(zero)(negOp)(mul)(one) |- RingDefs.commutativeMul(R)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.commRing.definition)
  }

  val mul_comm_of_commRing = Theorem(
    (Defs.commRing(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R) |- (x * y) === (y * x)
  ) {
    val cr = assume(Defs.commRing(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    have(RingDefs.commutativeMul(R)(mul)) by Tautology.from(commRing_mul_comm, cr)
    thenHave(forall(x, (x ∈ R) ==> forall(y, (y ∈ R) ==> ((x * y) === (y * x))))) by Substitute(
      RingDefs.commutativeMul.definition of (R := R, mul := mul)
    )
    val comm = lastStep

    val commAtX = have((x ∈ R) ==> forall(y, (y ∈ R) ==> ((x * y) === (y * x)))) by Tautology.from(comm of x)
    val commAtXForallY = have(forall(y, (y ∈ R) ==> ((x * y) === (y * x)))) by Tautology.from(commAtX, hx)
    val commAtXY = have((y ∈ R) ==> ((x * y) === (y * x))) by Tautology.from(commAtXForallY of y)

    have(thesis) by Tautology.from(commAtXY, hy)
  }
}
