package lisa.maths.MathlibPort.Algebra.Ring.Semiring

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Small “semiring API” derived from [[Defs.semiring]].
 */
object SemiringTheoremsSetLike extends lisa.Main {

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

  val add_closed = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- (x + y) ∈ R
  ) {
    have(thesis) by Tautology.from(AddTheoremsSetLike.add_closed_of_semiring)
  }

  val mul_closed = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- (x * y) ∈ R
  ) {
    have(thesis) by Tautology.from(MulTheoremsSetLike.mul_closed_of_semiring)
  }

  val mul_add = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (x * (y + z)) === ((x * y) + (x * z))
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.mul_add)
  }

  val add_mul = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- ((x + y) * z) === ((x * z) + (y * z))
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.add_mul)
  }

  val mul_zero = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (x * zero) === zero
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.mul_zero)
  }

  val zero_mul = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (zero * x) === zero
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.zero_mul)
  }

  val one_mul = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (one * x) === x
  ) {
    have(thesis) by Tautology.from(MulTheoremsSetLike.one_mul_of_semiring)
  }

  val mul_one = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (x * one) === x
  ) {
    have(thesis) by Tautology.from(MulTheoremsSetLike.mul_one_of_semiring)
  }

  val mul_assoc = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- ((x * y) * z) === (x * (y * z))
  ) {
    have(thesis) by Tautology.from(MulTheoremsSetLike.mul_assoc_of_semiring)
  }

  val add_assoc = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- ((x + y) + z) === (x + (y + z))
  ) {
    have(thesis) by Tautology.from(AddTheoremsSetLike.add_assoc_of_semiring)
  }

  val add_comm = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- (x + y) === (y + x)
  ) {
    have(thesis) by Tautology.from(AddTheoremsSetLike.add_comm_of_semiring)
  }

  val add_zero = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (x + zero) === x
  ) {
    have(thesis) by Tautology.from(AddTheoremsSetLike.add_zero_of_semiring)
  }

  val zero_add = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- (zero + x) === x
  ) {
    have(thesis) by Tautology.from(AddTheoremsSetLike.zero_add_of_semiring)
  }

  val commSemiring_isSemiring = Theorem(
    Defs.commSemiring(R)(add)(zero)(mul)(one) |- Defs.semiring(R)(add)(zero)(mul)(one)
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.commSemiring_isSemiring)
  }

  val mul_comm_of_commSemiring = Theorem(
    (Defs.commSemiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- (x * y) === (y * x)
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.commSemiring_mul_comm)
  }
}

