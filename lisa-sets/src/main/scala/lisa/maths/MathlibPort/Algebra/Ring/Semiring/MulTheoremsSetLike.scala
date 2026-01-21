package lisa.maths.MathlibPort.Algebra.Ring.Semiring

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.MathlibPort.Algebra.Ring.MulMonoidTheoremsSetLike
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Multiplicative theorems derived from [[Defs.semiring]] (via `mulMonoid`).
 */
object MulTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val mulMonoid_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.mulMonoid(R)(mul)(one)
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.semiring_mulMonoid)
  }

  val hasMul_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.hasMul(R)(mul)
  ) {
    have(thesis) by Tautology.from(mulMonoid_of_semiring, RingDefs.mulMonoid.definition, RingDefs.mulSemigroup.definition)
  }

  val one_mem_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- one ∈ R
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    have(RingDefs.mulMonoid(R)(mul)(one)) by Tautology.from(mulMonoid_of_semiring, s)
    have(thesis) by Tautology.from(MulMonoidTheoremsSetLike.one_mem_of_mulMonoid of (R := R, mul := mul, one := one), lastStep)
  }

  val mul_closed_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- (x * y) ∈ R
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    have(RingDefs.hasMul(R)(mul)) by Tautology.from(hasMul_of_semiring, s)
    have(thesis) by Tautology.from(MulMonoidTheoremsSetLike.mul_closed of (R := R, mul := mul, x := x, y := y), lastStep, hx, hy)
  }

  val one_mul_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- ((one * x) === x)
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)

    have(RingDefs.mulMonoid(R)(mul)(one)) by Tautology.from(mulMonoid_of_semiring, s)
    val oneMul = have(forall(x, (x ∈ R) ==> ((one * x) === x))) by Tautology.from(
      MulMonoidTheoremsSetLike.one_mul_of_mulMonoid of (R := R, mul := mul, one := one),
      lastStep
    )
    have(thesis) by Tautology.from(oneMul of x, hx)
  }

  val mul_one_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- ((x * one) === x)
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)

    have(RingDefs.mulMonoid(R)(mul)(one)) by Tautology.from(mulMonoid_of_semiring, s)
    val mulOne = have(forall(x, (x ∈ R) ==> ((x * one) === x))) by Tautology.from(
      MulMonoidTheoremsSetLike.mul_one_of_mulMonoid of (R := R, mul := mul, one := one),
      lastStep
    )
    have(thesis) by Tautology.from(mulOne of x, hx)
  }

  val mul_assoc_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (((x * y) * z) === (x * (y * z)))
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)

    have(RingDefs.mulMonoid(R)(mul)(one)) by Tautology.from(mulMonoid_of_semiring, s)
    have(RingDefs.mulSemigroup(R)(mul)) by Tautology.from(RingDefs.mulMonoid.definition, lastStep)
    have(RingDefs.associativeMul(R)(mul)) by Tautology.from(RingDefs.mulSemigroup.definition, lastStep)
    thenHave(
      forall(
        x,
        (x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x * y) * z) === (x * (y * z)))))
      )
    ) by Substitute(RingDefs.associativeMul.definition of (R := R, mul := mul))

    val assocAtX = have((x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x * y) * z) === (x * (y * z)))))) by Tautology.from(
      lastStep of x
    )
    val assocAtXForallY = have(forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x * y) * z) === (x * (y * z)))))) by Tautology.from(assocAtX, hx)
    val assocAtXY = have((y ∈ R) ==> forall(z, (z ∈ R) ==> (((x * y) * z) === (x * (y * z))))) by Tautology.from(assocAtXForallY of y)
    val assocAtXYForallZ = have(forall(z, (z ∈ R) ==> (((x * y) * z) === (x * (y * z))))) by Tautology.from(assocAtXY, hy)
    val assocAtXYZ = have((z ∈ R) ==> (((x * y) * z) === (x * (y * z)))) by Tautology.from(assocAtXYForallZ of z)

    have(thesis) by Tautology.from(assocAtXYZ, hz)
  }

  val mul_comm_of_commSemiring = Theorem(
    (Defs.commSemiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- ((x * y) === (y * x))
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.commSemiring_mul_comm)
  }
}

