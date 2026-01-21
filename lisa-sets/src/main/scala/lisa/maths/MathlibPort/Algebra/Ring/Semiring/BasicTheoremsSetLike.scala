package lisa.maths.MathlibPort.Algebra.Ring.Semiring

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Basic projection theorems for [[Defs.semiring]].
 */
object BasicTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def +(b: Expr[Ind]): Expr[Ind] = addApp(a, b)
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val semiring_addCommMonoid = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.addCommMonoid(R)(add)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val semiring_mulMonoid = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.mulMonoid(R)(mul)(one)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val semiring_distrib = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.distrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val left_distrib_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.leftDistrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition, RingDefs.distrib.definition)
  }

  val right_distrib_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.rightDistrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition, RingDefs.distrib.definition)
  }

  val mulZero_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- Defs.mulZero(R)(mul)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val zeroMul_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- Defs.zeroMul(R)(mul)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val mul_add = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (x * (y + z)) === ((x * y) + (x * z))
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)

    have(RingDefs.leftDistrib(R)(add)(mul)) by Tautology.from(left_distrib_of_semiring, s)
    thenHave(
      forall(x, (x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))))
    ) by Substitute(RingDefs.leftDistrib.definition of (R := R, add := add, mul := mul))

    val distAtX = have((x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z)))))) by Tautology.from(
      lastStep of x
    )
    val distAtXForallY = have(forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z)))))) by Tautology.from(distAtX, hx)
    val distAtXY = have((y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))) by Tautology.from(distAtXForallY of y)
    val distAtXYForallZ = have(forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))) by Tautology.from(distAtXY, hy)
    val distAtXYZ = have((z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z)))) by Tautology.from(distAtXYForallZ of z)

    have(thesis) by Tautology.from(distAtXYZ, hz)
  }

  val add_mul = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- ((x + y) * z) === ((x * z) + (y * z))
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)

    have(RingDefs.rightDistrib(R)(add)(mul)) by Tautology.from(right_distrib_of_semiring, s)
    thenHave(
      forall(x, (x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z))))))
    ) by Substitute(RingDefs.rightDistrib.definition of (R := R, add := add, mul := mul))

    val distAtX = have((x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z)))))) by Tautology.from(
      lastStep of x
    )
    val distAtXForallY = have(forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z)))))) by Tautology.from(distAtX, hx)
    val distAtXY = have((y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z))))) by Tautology.from(distAtXForallY of y)
    val distAtXYForallZ = have(forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z))))) by Tautology.from(distAtXY, hy)
    val distAtXYZ = have((z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z)))) by Tautology.from(distAtXYForallZ of z)

    have(thesis) by Tautology.from(distAtXYZ, hz)
  }

  val mul_zero = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (x * zero) === zero
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)

    have(Defs.mulZero(R)(mul)(zero)) by Tautology.from(mulZero_of_semiring, s)
    thenHave(forall(x, (x ∈ R) ==> ((x * zero) === zero))) by Substitute(
      Defs.mulZero.definition of (R := R, mul := mul, zero := zero)
    )
    have(thesis) by Tautology.from(lastStep of x, hx)
  }

  val zero_mul = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (zero * x) === zero
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)

    have(Defs.zeroMul(R)(mul)(zero)) by Tautology.from(zeroMul_of_semiring, s)
    thenHave(forall(x, (x ∈ R) ==> ((zero * x) === zero))) by Substitute(
      Defs.zeroMul.definition of (R := R, mul := mul, zero := zero)
    )
    have(thesis) by Tautology.from(lastStep of x, hx)
  }

  val commSemiring_isSemiring = Theorem(
    Defs.commSemiring(R)(add)(zero)(mul)(one) |- Defs.semiring(R)(add)(zero)(mul)(one)
  ) {
    have(thesis) by Tautology.from(Defs.commSemiring.definition)
  }

  val commSemiring_mul_comm = Theorem(
    (Defs.commSemiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- (x * y) === (y * x)
  ) {
    val cs = assume(Defs.commSemiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    have(RingDefs.commutativeMul(R)(mul)) by Tautology.from(Defs.commSemiring.definition, cs)
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
