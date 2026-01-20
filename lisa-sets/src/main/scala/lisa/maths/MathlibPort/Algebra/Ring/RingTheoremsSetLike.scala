package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions

/**
 * Small “ring API” lemmas derived from [[Defs.ring]].
 */
object RingTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def negApp(a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(negOp)(a)

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def +(b: Expr[Ind]): Expr[Ind] = addApp(a, b)
    def negOf: Expr[Ind] = negApp(a)
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val mul_add = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (x * (y + z)) === ((x * y) + (x * z))
  ) {
    have(thesis) by Tautology.from(DistribTheoremsSetLike.mul_add)
  }

  val add_mul = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (((x + y) * z) === ((x * z) + (y * z)))
  ) {
    have(thesis) by Tautology.from(DistribTheoremsSetLike.add_mul)
  }

  val mul_zero = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R) |- (x * zero) === zero
  ) {
    have(thesis) by Tautology.from(ZeroMulTheoremsSetLike.mul_zero_of_ring)
  }

  val zero_mul = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R) |- (zero * x) === zero
  ) {
    have(thesis) by Tautology.from(ZeroMulTheoremsSetLike.zero_mul_of_ring)
  }

  val mul_neg = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R) |- (x * y.negOf) === (x * y).negOf
  ) {
    have(thesis) by Tautology.from(NegMulTheoremsSetLike.mul_neg_of_ring)
  }

  val neg_mul = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R) |- (x.negOf * y) === (x * y).negOf
  ) {
    have(thesis) by Tautology.from(NegMulTheoremsSetLike.neg_mul_of_ring)
  }

  val neg_mul_neg = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R) |- (x.negOf * y.negOf) === (x * y)
  ) {
    have(thesis) by Tautology.from(NegMulTheoremsSetLike.neg_mul_neg_of_ring)
  }
}
