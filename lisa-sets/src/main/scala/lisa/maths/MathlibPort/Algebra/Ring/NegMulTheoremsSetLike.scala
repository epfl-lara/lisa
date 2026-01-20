package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Derive `x * (-y) = -(x*y)` and `(-x) * y = -(x*y)` from ring axioms.
 */
object NegMulTheoremsSetLike extends lisa.Main {

  import AddGroupCancelSetLike.neg_neg_of_addGroup
  import AddGroupCancelSetLike.eq_neg_of_add_eq_zero
  import AddGroupTheoremsSetLike.{add_closed, neg_mem_of_addGroup, right_neg_of_addGroup, zero_mem_of_addMonoid}
  import DistribTheoremsSetLike.{add_mul, mul_add}
  import MulMonoidTheoremsSetLike.{hasMul_of_mulMonoid, mul_closed}
  import ZeroMulTheoremsSetLike.{mul_zero_of_ring, zero_mul_of_ring}

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]

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

  val mul_neg_of_ring = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R) |- (x * y.negOf) === (x * y).negOf
  ) {
    val r = assume(Defs.ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    val addCG = have(Defs.addCommGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.ring.definition, r)
    val addG = have(Defs.addGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.addCommGroup.definition, addCG)
    val addM = have(Defs.addMonoid(R)(add)(zero)) by Tautology.from(AddGroupTheoremsSetLike.addMonoid_of_addGroup, addG)
    val zeroInR = have(zero ∈ R) by Tautology.from(zero_mem_of_addMonoid, addM)

    val mulM = have(Defs.mulMonoid(R)(mul)(one)) by Tautology.from(Defs.ring.definition, r)
    val hasMulR = have(Defs.hasMul(R)(mul)) by Tautology.from(hasMul_of_mulMonoid, mulM)

    val negMem = have(forall(y, (y ∈ R) ==> (y.negOf ∈ R))) by Tautology.from(neg_mem_of_addGroup, addG)
    val negyInR = have(y.negOf ∈ R) by Tautology.from(negMem of y, hy)

    val xyInR = have((x * y) ∈ R) by Tautology.from(mul_closed of (x := x, y := y), hasMulR, hx, hy)
    val xnegyInR = have((x * y.negOf) ∈ R) by Tautology.from(mul_closed of (x := x, y := y.negOf), hasMulR, hx, negyInR)

    val rightNeg = have(forall(y, (y ∈ R) ==> ((y + y.negOf) === zero))) by Tautology.from(right_neg_of_addGroup, addG)
    val yAddNeg = have((y + y.negOf) === zero) by Tautology.from(rightNeg of y, hy)

    val step0 = have((x * (y + y.negOf)) === ((x * y) + (x * y.negOf))) by Tautology.from(
      mul_add of (R := R, add := add, zero := zero, negOp := negOp, mul := mul, one := one, x := x, y := y, z := y.negOf),
      r,
      hx,
      hy,
      negyInR
    )
    val step1 = have((x * (y + y.negOf)) === (x * zero)) by Congruence.from(yAddNeg)
    val step2 = have((x * zero) === zero) by Tautology.from(mul_zero_of_ring, r, hx)
    val step3 = have(((x * y) + (x * y.negOf)) === zero) by Congruence.from(step0, step1, step2)

    have(thesis) by Tautology.from(
      eq_neg_of_add_eq_zero of (R := R, add := add, zero := zero, negOp := negOp, x := (x * y), y := (x * y.negOf)),
      addG,
      xyInR,
      xnegyInR,
      step3
    )
  }

  val neg_mul_of_ring = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R) |- (x.negOf * y) === (x * y).negOf
  ) {
    val r = assume(Defs.ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    val addCG = have(Defs.addCommGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.ring.definition, r)
    val addG = have(Defs.addGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.addCommGroup.definition, addCG)
    val addM = have(Defs.addMonoid(R)(add)(zero)) by Tautology.from(AddGroupTheoremsSetLike.addMonoid_of_addGroup, addG)
    val zeroInR = have(zero ∈ R) by Tautology.from(zero_mem_of_addMonoid, addM)

    val mulM = have(Defs.mulMonoid(R)(mul)(one)) by Tautology.from(Defs.ring.definition, r)
    val hasMulR = have(Defs.hasMul(R)(mul)) by Tautology.from(hasMul_of_mulMonoid, mulM)

    val negMem = have(forall(x, (x ∈ R) ==> (x.negOf ∈ R))) by Tautology.from(neg_mem_of_addGroup, addG)
    val negxInR = have(x.negOf ∈ R) by Tautology.from(negMem of x, hx)

    val xyInR = have((x * y) ∈ R) by Tautology.from(mul_closed of (x := x, y := y), hasMulR, hx, hy)
    val negxYInR = have((x.negOf * y) ∈ R) by Tautology.from(mul_closed of (x := x.negOf, y := y), hasMulR, negxInR, hy)

    val rightNeg = have(forall(x, (x ∈ R) ==> ((x + x.negOf) === zero))) by Tautology.from(right_neg_of_addGroup, addG)
    val xAddNeg = have((x + x.negOf) === zero) by Tautology.from(rightNeg of x, hx)

    val step0 = have((((x + x.negOf) * y) === ((x * y) + (x.negOf * y)))) by Tautology.from(
      add_mul of (R := R, add := add, zero := zero, negOp := negOp, mul := mul, one := one, x := x, y := x.negOf, z := y),
      r,
      hx,
      negxInR,
      hy
    )
    val step1 = have(((x + x.negOf) * y) === (zero * y)) by Congruence.from(xAddNeg)
    val step2 = have((zero * y) === zero) by Tautology.from(zero_mul_of_ring of (x := y), r, hy)
    val step3 = have(((x * y) + (x.negOf * y)) === zero) by Congruence.from(step0, step1, step2)

    have(thesis) by Tautology.from(
      eq_neg_of_add_eq_zero of (R := R, add := add, zero := zero, negOp := negOp, x := (x * y), y := (x.negOf * y)),
      addG,
      xyInR,
      negxYInR,
      step3
    )
  }

  val neg_mul_neg_of_ring = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R) |- (x.negOf * y.negOf) === (x * y)
  ) {
    val r = assume(Defs.ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    val addCG = have(Defs.addCommGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.ring.definition, r)
    val addG = have(Defs.addGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.addCommGroup.definition, addCG)

    val mulM = have(Defs.mulMonoid(R)(mul)(one)) by Tautology.from(Defs.ring.definition, r)
    val hasMulR = have(Defs.hasMul(R)(mul)) by Tautology.from(hasMul_of_mulMonoid, mulM)

    val negMem = have(forall(x, (x ∈ R) ==> (x.negOf ∈ R))) by Tautology.from(neg_mem_of_addGroup, addG)
    val negxInR = have(x.negOf ∈ R) by Tautology.from(negMem of x, hx)
    val negyInR = have(y.negOf ∈ R) by Tautology.from(negMem of y, hy)

    val xyInR = have((x * y) ∈ R) by Tautology.from(mul_closed of (x := x, y := y), hasMulR, hx, hy)

    val step1 = have((x.negOf * y.negOf) === (x * y.negOf).negOf) by Tautology.from(
      neg_mul_of_ring of (R := R, add := add, zero := zero, negOp := negOp, mul := mul, one := one, x := x, y := y.negOf),
      r,
      hx,
      negyInR
    )

    val step2 = have((x * y.negOf) === (x * y).negOf) by Tautology.from(
      mul_neg_of_ring of (R := R, add := add, zero := zero, negOp := negOp, mul := mul, one := one, x := x, y := y),
      r,
      hx,
      hy
    )

    val step2n = have((x * y.negOf).negOf === ((x * y).negOf).negOf) by Congruence.from(step2)
    val step3 = have(((x * y).negOf).negOf === (x * y)) by Tautology.from(
      neg_neg_of_addGroup of (R := R, add := add, zero := zero, negOp := negOp, x := (x * y)),
      addG,
      xyInR
    )

    have(thesis) by Congruence.from(step1, step2n, step3)
  }
}
