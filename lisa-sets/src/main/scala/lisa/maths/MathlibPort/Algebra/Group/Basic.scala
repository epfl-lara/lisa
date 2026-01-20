package lisa.maths.MathlibPort.Algebra.Group

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Group/Basic`.
 *
 * This file starts with an untyped (single-sorted) group operation `mul` and
 * proves basic consequences from standard axioms, as a stepping stone before
 * moving to set-based carriers and set-coded structures.
 */
object Basic extends lisa.Main {

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val one = variable[Ind]
  val inv = variable[Ind >>: Ind]
  val mul = variable[Ind >>: Ind >>: Ind]

  extension (a: Expr[Ind]) {
    inline def invOf: Expr[Ind] = App(inv, a)
    infix inline def *(b: Expr[Ind]): Expr[Ind] = App(App(mul, a), b)
  }

  val mul_assoc = forall(x, forall(y, forall(z, ((x * y) * z) === (x * (y * z)))))
  val one_mul = forall(x, (one * x) === x)
  val mul_one = forall(x, (x * one) === x)
  val mul_left_inv = forall(x, (x.invOf * x) === one)

  val mul_left_cancel = Theorem((mul_assoc, one_mul, mul_left_inv) |- ((x * y) === (x * z)) ==> (y === z)) {
    val assoc = assume(mul_assoc)
    val oneMul = assume(one_mul)
    val leftInv = assume(mul_left_inv)

    val h = assume((x * y) === (x * z))

    val hF = (x * y) === (x * z)
    val eq1F = (x.invOf * (x * y)) === (x.invOf * (x * z))
    val assocYF = ((x.invOf * x) * y) === (x.invOf * (x * y))
    val assocZF = ((x.invOf * x) * z) === (x.invOf * (x * z))
    val invxF = (x.invOf * x) === one
    val oneYF = (one * y) === y
    val oneZF = (one * z) === z

    val eq1 = have(eq1F) by Congruence
    val assocY = have(assocYF) by Tautology.from(assoc of x.invOf of x of y)
    val assocZ = have(assocZF) by Tautology.from(assoc of x.invOf of x of z)
    val invx = have(invxF) by Tautology.from(leftInv of x)
    val oneY = have(oneYF) by Tautology.from(oneMul of y)
    val oneZ = have(oneZF) by Tautology.from(oneMul of z)

    var seq = Set(mul_assoc, one_mul, mul_left_inv, hF, eq1F, assocYF, assocZF, invxF, oneYF, oneZF) |- Set(y === z)
    have(seq) by Congruence

    seq = (seq.left - eq1F) ++ eq1.statement.left |- seq.right
    have(seq) by Cut(eq1, lastStep)
    seq = (seq.left - assocYF) ++ assocY.statement.left |- seq.right
    have(seq) by Cut(assocY, lastStep)
    seq = (seq.left - assocZF) ++ assocZ.statement.left |- seq.right
    have(seq) by Cut(assocZ, lastStep)
    seq = (seq.left - invxF) ++ invx.statement.left |- seq.right
    have(seq) by Cut(invx, lastStep)
    seq = (seq.left - oneYF) ++ oneY.statement.left |- seq.right
    have(seq) by Cut(oneY, lastStep)
    seq = (seq.left - oneZF) ++ oneZ.statement.left |- seq.right
    have(seq) by Cut(oneZ, lastStep)

    thenHave(thesis) by RightImplies.withParameters(hF, y === z)
  }

  val mul_eq_one_iff_eq_inv = Theorem((mul_assoc, one_mul, mul_one, mul_left_inv) |- ((x * y) === one) ==> (y === x.invOf)) {
    val assoc = assume(mul_assoc)
    val oneMul = assume(one_mul)
    val mulOne = assume(mul_one)
    val leftInv = assume(mul_left_inv)

    val h = assume((x * y) === one)

    val oneY = have((one * y) === y) by Tautology.from(oneMul of y)
    val assocY = have(((x.invOf * x) * y) === (x.invOf * (x * y))) by Tautology.from(assoc of x.invOf of x of y)
    val invx = have((x.invOf * x) === one) by Tautology.from(leftInv of x)
    val invxOne = have((x.invOf * one) === x.invOf) by Tautology.from(mulOne of x.invOf)
    val step1 = have((x.invOf * (x * y)) === (x.invOf * one)) by Congruence.from(h)

    have(y === x.invOf) by Congruence.from(step1, assocY, invx, oneY, invxOne)
    thenHave(thesis) by RightImplies.withParameters((x * y) === one, y === x.invOf)
  }
}
