package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Derive `x*0 = 0` and `0*x = 0` from the ring axioms.
 */
object ZeroMulTheoremsSetLike extends lisa.Main {

  import AddGroupCancelSetLike.eq_zero_of_eq_add_self
  import AddGroupTheoremsSetLike.{addMonoid_of_addGroup, left_zero_of_addMonoid, right_zero_of_addMonoid, zero_mem_of_addMonoid}
  import DistribTheoremsSetLike.{add_mul, mul_add}
  import MulMonoidTheoremsSetLike.{hasMul_of_mulMonoid, mul_closed}

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def +(b: Expr[Ind]): Expr[Ind] = addApp(a, b)
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val mul_zero_of_ring = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R) |- (x * zero) === zero
  ) {
    val r = assume(Defs.ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)

    val addCG = have(Defs.addCommGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.ring.definition, r)
    val addG = have(Defs.addGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.addCommGroup.definition, addCG)
    val addM = have(Defs.addMonoid(R)(add)(zero)) by Tautology.from(AddGroupTheoremsSetLike.addMonoid_of_addGroup, addG)

    val zeroInR = have(zero ∈ R) by Tautology.from(zero_mem_of_addMonoid, addM)

    val mulM = have(Defs.mulMonoid(R)(mul)(one)) by Tautology.from(Defs.ring.definition, r)
    val hasMulR = have(Defs.hasMul(R)(mul)) by Tautology.from(hasMul_of_mulMonoid, mulM)
    val x0InR = have((x * zero) ∈ R) by Tautology.from(mul_closed of (x := x, y := zero), hasMulR, hx, zeroInR)

    val leftZero = have(forall(x, (x ∈ R) ==> ((zero + x) === x))) by Tautology.from(left_zero_of_addMonoid, addM)
    val zeroAdd = have((zero + zero) === zero) by Tautology.from(leftZero of zero, zeroInR)

    val dist = have((x * (zero + zero)) === ((x * zero) + (x * zero))) by Tautology.from(
      mul_add of (R := R, add := add, zero := zero, negOp := negOp, mul := mul, one := one, x := x, y := zero, z := zero),
      r,
      hx,
      zeroInR,
      zeroInR
    )

    val leftEq = have((x * (zero + zero)) === (x * zero)) by Congruence.from(zeroAdd)
    val h = have((x * zero) === ((x * zero) + (x * zero))) by Congruence.from(leftEq, dist)

    have(thesis) by Tautology.from(eq_zero_of_eq_add_self of (R := R, add := add, zero := zero, negOp := negOp, x := (x * zero)), addG, x0InR, h)
  }

  val zero_mul_of_ring = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R) |- (zero * x) === zero
  ) {
    val r = assume(Defs.ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)

    val addCG = have(Defs.addCommGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.ring.definition, r)
    val addG = have(Defs.addGroup(R)(add)(zero)(negOp)) by Tautology.from(Defs.addCommGroup.definition, addCG)
    val addM = have(Defs.addMonoid(R)(add)(zero)) by Tautology.from(AddGroupTheoremsSetLike.addMonoid_of_addGroup, addG)

    val zeroInR = have(zero ∈ R) by Tautology.from(zero_mem_of_addMonoid, addM)

    val mulM = have(Defs.mulMonoid(R)(mul)(one)) by Tautology.from(Defs.ring.definition, r)
    val hasMulR = have(Defs.hasMul(R)(mul)) by Tautology.from(hasMul_of_mulMonoid, mulM)
    val x0InR = have((zero * x) ∈ R) by Tautology.from(mul_closed of (x := zero, y := x), hasMulR, zeroInR, hx)

    val leftZero = have(forall(x, (x ∈ R) ==> ((zero + x) === x))) by Tautology.from(left_zero_of_addMonoid, addM)
    val addZero = have((zero + zero) === zero) by Tautology.from(leftZero of zero, zeroInR)

    val dist = have(((zero + zero) * x) === ((zero * x) + (zero * x))) by Tautology.from(
      add_mul of (R := R, add := add, zero := zero, negOp := negOp, mul := mul, one := one, x := zero, y := zero, z := x),
      r,
      zeroInR,
      zeroInR,
      hx
    )

    val leftEq = have(((zero + zero) * x) === (zero * x)) by Congruence.from(addZero)
    val h = have((zero * x) === ((zero * x) + (zero * x))) by Congruence.from(leftEq, dist)

    have(thesis) by Tautology.from(eq_zero_of_eq_add_self of (R := R, add := add, zero := zero, negOp := negOp, x := (zero * x)), addG, x0InR, h)
  }
}
