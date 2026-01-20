package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Cancellation and equation-solving lemmas for the additive group structure in [[Defs]].
 *
 * This file is intentionally self-contained (derives everything from [[Defs]] by unfolding).
 */
object AddGroupCancelSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]
  private val t = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def negApp(a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(negOp)(a)

  extension (a: Expr[Ind]) {
    infix def +(b: Expr[Ind]): Expr[Ind] = addApp(a, b)
    def negOf: Expr[Ind] = negApp(a)
  }

  val addMonoid_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- Defs.addMonoid(R)(add)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition)
  }

  val assoc_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- Defs.associativeAdd(R)(add)
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition, Defs.addMonoid.definition, Defs.addSemigroup.definition)
  }

  val left_zero_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(t, (t ∈ R) ==> ((zero + t) === t))
  ) {
    val g = assume(Defs.addGroup(R)(add)(zero)(negOp))
    val mon = have(Defs.addMonoid(R)(add)(zero)) by Tautology.from(addMonoid_of_addGroup, g)
    val lz = have(Defs.leftZero(R)(add)(zero)) by Tautology.from(Defs.addMonoid.definition, mon)
    thenHave(forall(t, (t ∈ R) ==> ((zero + t) === t))) by Substitute(Defs.leftZero.definition of (R := R, add := add, zero := zero))
    thenHave(thesis) by Restate
  }

  val right_zero_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(t, (t ∈ R) ==> ((t + zero) === t))
  ) {
    val g = assume(Defs.addGroup(R)(add)(zero)(negOp))
    val mon = have(Defs.addMonoid(R)(add)(zero)) by Tautology.from(addMonoid_of_addGroup, g)
    val rz = have(Defs.rightZero(R)(add)(zero)) by Tautology.from(Defs.addMonoid.definition, mon)
    thenHave(forall(t, (t ∈ R) ==> ((t + zero) === t))) by Substitute(Defs.rightZero.definition of (R := R, add := add, zero := zero))
    thenHave(thesis) by Restate
  }

  val left_neg_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(x, (x ∈ R) ==> ((x.negOf + x) === zero))
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition, Defs.leftNeg.definition)
  }

  val neg_mem_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(x, (x ∈ R) ==> (x.negOf ∈ R))
  ) {
    assume(Defs.addGroup(R)(add)(zero)(negOp))
    have(Defs.hasNeg(R)(negOp)) by Tautology.from(Defs.addGroup.definition)
    thenHave(negOp :: R -> R) by Substitute(Defs.hasNeg.definition)
    thenHave(x ∈ R |- x.negOf ∈ R) by Tautology.fromLastStep(
      Functions.BasicTheorems.appTyping of (f := negOp, A := R, B := R, x := x)
    )
    thenHave((x ∈ R) ==> (x.negOf ∈ R)) by RightImplies
    thenHave(thesis) by RightForall
  }

  val add_left_cancel_of_addGroup = Theorem(
    (Defs.addGroup(R)(add)(zero)(negOp), x ∈ R, y ∈ R, z ∈ R, (x + y) === (x + z)) |- y === z
  ) {
    val g = assume(Defs.addGroup(R)(add)(zero)(negOp))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)
    val h = assume((x + y) === (x + z))

    have(Defs.associativeAdd(R)(add)) by Tautology.from(assoc_of_addGroup, g)
    thenHave(
      forall(a, (a ∈ R) ==> forall(b, (b ∈ R) ==> forall(c, (c ∈ R) ==> (((a + b) + c) === (a + (b + c))))))
    ) by Substitute(Defs.associativeAdd.definition of (R := R, add := add))
    val assoc = lastStep

    val negMem = have(forall(x, (x ∈ R) ==> (x.negOf ∈ R))) by Tautology.from(neg_mem_of_addGroup, g)
    val negxInR = have(x.negOf ∈ R) by Tautology.from(negMem of x, hx)

    val leftNeg = have(forall(x, (x ∈ R) ==> ((x.negOf + x) === zero))) by Tautology.from(left_neg_of_addGroup, g)
    val leftNegx = have((x.negOf + x) === zero) by Tautology.from(leftNeg of x, hx)

    val leftZero = have(forall(t, (t ∈ R) ==> ((zero + t) === t))) by Tautology.from(left_zero_of_addGroup, g)

    val step0 = have((x.negOf + (x + y)) === (x.negOf + (x + z))) by Congruence.from(h)

    val assocAtNegx = have(
      forall(
        b,
        (b ∈ R) ==> forall(c, (c ∈ R) ==> (((x.negOf + b) + c) === (x.negOf + (b + c))))
      )
    ) by Tautology.from(assoc of x.negOf, negxInR)
    val assocAtNegxX = have(forall(c, (c ∈ R) ==> (((x.negOf + x) + c) === (x.negOf + (x + c))))) by Tautology.from(
      assocAtNegx of x,
      hx
    )

    val assocEqY = have(((x.negOf + x) + y) === (x.negOf + (x + y))) by Tautology.from(assocAtNegxX of y, hy)
    val assocEqZ = have(((x.negOf + x) + z) === (x.negOf + (x + z))) by Tautology.from(assocAtNegxX of z, hz)
    val step1 = have((x.negOf + (x + y)) === ((x.negOf + x) + y)) by Congruence.from(assocEqY)
    val step2 = have((x.negOf + (x + z)) === ((x.negOf + x) + z)) by Congruence.from(assocEqZ)

    val step3 = have(((x.negOf + x) + y) === (zero + y)) by Congruence.from(leftNegx)
    val step4 = have(((x.negOf + x) + z) === (zero + z)) by Congruence.from(leftNegx)

    val step5 = have((zero + y) === y) by Tautology.from(leftZero of y, hy)
    val step6 = have((zero + z) === z) by Tautology.from(leftZero of z, hz)

    have(thesis) by Congruence.from(step0, step1, step2, step3, step4, step5, step6)
  }

  val eq_zero_of_eq_add_self = Theorem(
    (Defs.addGroup(R)(add)(zero)(negOp), x ∈ R, x === (x + x)) |- x === zero
  ) {
    val g = assume(Defs.addGroup(R)(add)(zero)(negOp))
    val hx = assume(x ∈ R)
    val h = assume(x === (x + x))

    have(Defs.associativeAdd(R)(add)) by Tautology.from(assoc_of_addGroup, g)
    thenHave(
      forall(a, (a ∈ R) ==> forall(b, (b ∈ R) ==> forall(c, (c ∈ R) ==> (((a + b) + c) === (a + (b + c))))))
    ) by Substitute(Defs.associativeAdd.definition of (R := R, add := add))
    val assoc = lastStep

    val negMem = have(forall(x, (x ∈ R) ==> (x.negOf ∈ R))) by Tautology.from(neg_mem_of_addGroup, g)
    val negxInR = have(x.negOf ∈ R) by Tautology.from(negMem of x, hx)

    val leftNeg = have(forall(x, (x ∈ R) ==> ((x.negOf + x) === zero))) by Tautology.from(left_neg_of_addGroup, g)
    val leftNegx = have((x.negOf + x) === zero) by Tautology.from(leftNeg of x, hx)

    val leftZero = have(forall(t, (t ∈ R) ==> ((zero + t) === t))) by Tautology.from(left_zero_of_addGroup, g)

    val step0 = have((x.negOf + x) === (x.negOf + (x + x))) by Congruence.from(h)
    val assocAtNegx = have(
      forall(
        b,
        (b ∈ R) ==> forall(c, (c ∈ R) ==> (((x.negOf + b) + c) === (x.negOf + (b + c))))
      )
    ) by Tautology.from(assoc of x.negOf, negxInR)
    val assocAtNegxX = have(forall(c, (c ∈ R) ==> (((x.negOf + x) + c) === (x.negOf + (x + c))))) by Tautology.from(
      assocAtNegx of x,
      hx
    )
    val assocEqX = have(((x.negOf + x) + x) === (x.negOf + (x + x))) by Tautology.from(assocAtNegxX of x, hx)
    val step1 = have((x.negOf + (x + x)) === ((x.negOf + x) + x)) by Congruence.from(assocEqX)
    val step2 = have(((x.negOf + x) + x) === (zero + x)) by Congruence.from(leftNegx)
    val step3 = have((zero + x) === x) by Tautology.from(leftZero of x, hx)

    val step4 = have((x.negOf + x) === x) by Congruence.from(step0, step1, step2, step3)
    have(thesis) by Congruence.from(leftNegx, step4)
  }

  val eq_neg_of_add_eq_zero = Theorem(
    (Defs.addGroup(R)(add)(zero)(negOp), x ∈ R, y ∈ R, (x + y) === zero) |- y === x.negOf
  ) {
    val g = assume(Defs.addGroup(R)(add)(zero)(negOp))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val h = assume((x + y) === zero)

    have(Defs.associativeAdd(R)(add)) by Tautology.from(assoc_of_addGroup, g)
    thenHave(
      forall(a, (a ∈ R) ==> forall(b, (b ∈ R) ==> forall(c, (c ∈ R) ==> (((a + b) + c) === (a + (b + c))))))
    ) by Substitute(Defs.associativeAdd.definition of (R := R, add := add))
    val assoc = lastStep

    val negMem = have(forall(x, (x ∈ R) ==> (x.negOf ∈ R))) by Tautology.from(neg_mem_of_addGroup, g)
    val negxInR = have(x.negOf ∈ R) by Tautology.from(negMem of x, hx)

    val leftNeg = have(forall(x, (x ∈ R) ==> ((x.negOf + x) === zero))) by Tautology.from(left_neg_of_addGroup, g)
    val leftNegx = have((x.negOf + x) === zero) by Tautology.from(leftNeg of x, hx)

    val leftZero = have(forall(t, (t ∈ R) ==> ((zero + t) === t))) by Tautology.from(left_zero_of_addGroup, g)
    val rightZero = have(forall(t, (t ∈ R) ==> ((t + zero) === t))) by Tautology.from(right_zero_of_addGroup, g)

    val step0 = have((x.negOf + (x + y)) === (x.negOf + zero)) by Congruence.from(h)
    val assocAtNegx = have(
      forall(
        b,
        (b ∈ R) ==> forall(c, (c ∈ R) ==> (((x.negOf + b) + c) === (x.negOf + (b + c))))
      )
    ) by Tautology.from(assoc of x.negOf, negxInR)
    val assocAtNegxX = have(forall(c, (c ∈ R) ==> (((x.negOf + x) + c) === (x.negOf + (x + c))))) by Tautology.from(
      assocAtNegx of x,
      hx
    )
    val assocEqY = have(((x.negOf + x) + y) === (x.negOf + (x + y))) by Tautology.from(assocAtNegxX of y, hy)
    val step1 = have((x.negOf + (x + y)) === ((x.negOf + x) + y)) by Congruence.from(assocEqY)
    val step2 = have(((x.negOf + x) + y) === (zero + y)) by Congruence.from(leftNegx)
    val step3 = have((zero + y) === y) by Tautology.from(leftZero of y, hy)
    val step4 = have((x.negOf + (x + y)) === y) by Congruence.from(step1, step2, step3)

    val step5 = have((x.negOf + zero) === x.negOf) by Tautology.from(rightZero of x.negOf, negxInR)
    have(thesis) by Congruence.from(step0, step4, step5)
  }

  val neg_neg_of_addGroup = Theorem(
    (Defs.addGroup(R)(add)(zero)(negOp), x ∈ R) |- x.negOf.negOf === x
  ) {
    val g = assume(Defs.addGroup(R)(add)(zero)(negOp))
    val hx = assume(x ∈ R)

    val negMem = have(forall(x, (x ∈ R) ==> (x.negOf ∈ R))) by Tautology.from(neg_mem_of_addGroup, g)
    val negxInR = have(x.negOf ∈ R) by Tautology.from(negMem of x, hx)

    val leftNeg = have(forall(x, (x ∈ R) ==> ((x.negOf + x) === zero))) by Tautology.from(left_neg_of_addGroup, g)
    val leftNegx = have((x.negOf + x) === zero) by Tautology.from(leftNeg of x, hx)

    val step0 = have(x === x.negOf.negOf) by Tautology.from(
      eq_neg_of_add_eq_zero of (R := R, add := add, zero := zero, negOp := negOp, x := x.negOf, y := x),
      g,
      negxInR,
      hx,
      leftNegx
    )

    have(thesis) by Tautology.from(step0)
  }
}
