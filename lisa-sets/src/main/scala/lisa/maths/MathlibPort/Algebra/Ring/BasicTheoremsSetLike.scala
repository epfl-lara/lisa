package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

import Defs.{addCommGroup, mulMonoid, ring}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Ring/Basic` (very small set-based fragment).
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

  val add_zero_of_addMonoid = Theorem(
    Defs.addMonoid(R)(add)(zero) |- forall(x, x ∈ R ==> ((x + zero) === x))
  ) {
    have(thesis) by Tautology.from(Defs.addMonoid.definition, Defs.rightZero.definition)
  }

  val zero_add_of_addMonoid = Theorem(
    Defs.addMonoid(R)(add)(zero) |- forall(x, x ∈ R ==> ((zero + x) === x))
  ) {
    have(thesis) by Tautology.from(Defs.addMonoid.definition, Defs.leftZero.definition)
  }

  val add_left_neg_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(x, x ∈ R ==> ((x.negOf + x) === zero))
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition, Defs.leftNeg.definition)
  }

  val add_right_neg_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(x, x ∈ R ==> ((x + x.negOf) === zero))
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition, Defs.rightNeg.definition)
  }

  val one_mul_of_mulMonoid = Theorem(
    mulMonoid(R)(mul)(one) |- forall(x, x ∈ R ==> ((one * x) === x))
  ) {
    have(thesis) by Tautology.from(Defs.mulMonoid.definition, Defs.leftOne.definition)
  }

  val mul_one_of_mulMonoid = Theorem(
    mulMonoid(R)(mul)(one) |- forall(x, x ∈ R ==> ((x * one) === x))
  ) {
    have(thesis) by Tautology.from(Defs.mulMonoid.definition, Defs.rightOne.definition)
  }

  val left_distrib_of_ring = Theorem(
    ring(R)(add)(zero)(negOp)(mul)(one) |- Defs.leftDistrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.ring.definition, Defs.distrib.definition)
  }

  val right_distrib_of_ring = Theorem(
    ring(R)(add)(zero)(negOp)(mul)(one) |- Defs.rightDistrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.ring.definition, Defs.distrib.definition)
  }

  val addCommGroup_of_ring = Theorem(
    ring(R)(add)(zero)(negOp)(mul)(one) |- addCommGroup(R)(add)(zero)(negOp)
  ) {
    have(thesis) by Tautology.from(Defs.ring.definition)
  }

  val mulMonoid_of_ring = Theorem(
    ring(R)(add)(zero)(negOp)(mul)(one) |- mulMonoid(R)(mul)(one)
  ) {
    have(thesis) by Tautology.from(Defs.ring.definition)
  }

  val mul_add = Theorem(
    (ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- ((x * (y + z)) === ((x * y) + (x * z)))
  ) {
    val r = assume(ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)

    have(Defs.leftDistrib(R)(add)(mul)) by Tautology.from(left_distrib_of_ring, r)
    thenHave(
      forall(
        x,
        x ∈ R ==> forall(y, y ∈ R ==> forall(z, z ∈ R ==> ((x * (y + z)) === ((x * y) + (x * z)))))
      )
    ) by Substitute(Defs.leftDistrib.definition of (R := R, add := add, mul := mul))

    val distAtX = have(
      (x ∈ R) ==> forall(
        y,
        (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))
      )
    ) by Tautology.from(lastStep of x)
    val distAtXForallY = have(
      forall(
        y,
        (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))
      )
    ) by Tautology.from(distAtX, hx)
    val distAtXY = have(
      (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))
    ) by Tautology.from(distAtXForallY of y)
    val distAtXYForallZ = have(
      forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))
    ) by Tautology.from(distAtXY, hy)
    val distAtXYZ = have((z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z)))) by Tautology.from(distAtXYForallZ of z)

    have(thesis) by Tautology.from(distAtXYZ, hz)
  }
}
