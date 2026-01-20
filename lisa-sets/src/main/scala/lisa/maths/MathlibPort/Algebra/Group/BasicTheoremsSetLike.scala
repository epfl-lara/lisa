package lisa.maths.MathlibPort.Algebra.Group

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

import Defs.{group, monoid, semigroup}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Group/Basic`.
 *
 * Basic derived facts for the set-based structure predicates in [[Defs]].
 */
object BasicTheoremsSetLike extends lisa.Main {

  val G = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]
  val inv = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  private def invApp(a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(inv)(a)

  extension (a: Expr[Ind]) {
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
    def invOf: Expr[Ind] = invApp(a)
  }

  val mul_closed = Theorem(
    (Defs.hasMul(G)(mul), x ∈ G, y ∈ G) |- (x * y) ∈ G
  ) {
    have(thesis) by Tautology.from(
      Defs.hasMul.definition,
      SetLike.mul_closed of (G := G, mul := mul, x := x, y := y)
    )
  }

  val assoc_of_semigroup = Theorem(
    semigroup(G)(mul) |- Defs.associative(G)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.semigroup.definition)
  }

  val one_mem_of_monoid = Theorem(
    monoid(G)(mul)(one) |- one ∈ G
  ) {
    have(thesis) by Tautology.from(
      Defs.monoid.definition,
      Defs.hasOne.definition
    )
  }

  val left_id_of_monoid = Theorem(
    monoid(G)(mul)(one) |- forall(x, x ∈ G ==> ((one * x) === x))
  ) {
    have(thesis) by Tautology.from(
      Defs.monoid.definition,
      Defs.leftIdentity.definition
    )
  }

  val right_id_of_monoid = Theorem(
    monoid(G)(mul)(one) |- forall(x, x ∈ G ==> ((x * one) === x))
  ) {
    have(thesis) by Tautology.from(
      Defs.monoid.definition,
      Defs.rightIdentity.definition
    )
  }

  val monoid_of_group = Theorem(
    group(G)(mul)(one)(inv) |- monoid(G)(mul)(one)
  ) {
    have(thesis) by Tautology.from(Defs.group.definition)
  }

  val assoc_of_group = Theorem(
    group(G)(mul)(one)(inv) |- Defs.associative(G)(mul)
  ) {
    have(thesis) by Tautology.from(
      assoc_of_semigroup,
      Defs.group.definition,
      Defs.monoid.definition
    )
  }

  val left_id_of_group = Theorem(
    group(G)(mul)(one)(inv) |- forall(x, x ∈ G ==> ((one * x) === x))
  ) {
    have(thesis) by Tautology.from(
      left_id_of_monoid,
      monoid_of_group
    )
  }

  val right_id_of_group = Theorem(
    group(G)(mul)(one)(inv) |- forall(x, x ∈ G ==> ((x * one) === x))
  ) {
    have(thesis) by Tautology.from(
      right_id_of_monoid,
      monoid_of_group
    )
  }

  val inv_mem_of_group = Theorem(
    group(G)(mul)(one)(inv) |- forall(x, x ∈ G ==> (x.invOf ∈ G))
  ) {
    assume(group(G)(mul)(one)(inv))
    have(Defs.hasInv(G)(inv)) by Tautology.from(Defs.group.definition)
    thenHave(inv :: G -> G) by Substitute(Defs.hasInv.definition)
    thenHave(x ∈ G |- x.invOf ∈ G) by Tautology.fromLastStep(
      Functions.BasicTheorems.appTyping of (f := inv, A := G, B := G, x := x)
    )
    thenHave(x ∈ G ==> (x.invOf ∈ G)) by RightImplies
    thenHave(thesis) by RightForall
  }

  val left_inv_of_group = Theorem(
    group(G)(mul)(one)(inv) |- forall(x, x ∈ G ==> ((x.invOf * x) === one))
  ) {
    have(thesis) by Tautology.from(
      Defs.group.definition,
      Defs.leftInverse.definition
    )
  }

  val right_inv_of_group = Theorem(
    group(G)(mul)(one)(inv) |- forall(x, x ∈ G ==> ((x * x.invOf) === one))
  ) {
    have(thesis) by Tautology.from(
      Defs.group.definition,
      Defs.rightInverse.definition
    )
  }

  val inv_mul_cancel_left = Theorem(
    (group(G)(mul)(one)(inv), x ∈ G, y ∈ G) |- ((x.invOf * (x * y)) === y)
  ) {
    val grp = assume(group(G)(mul)(one)(inv))
    val xInG = assume(x ∈ G)
    val yInG = assume(y ∈ G)

    val invMem = have(forall(x, x ∈ G ==> (x.invOf ∈ G))) by Tautology.from(inv_mem_of_group, grp)
    val invxInG = have(x.invOf ∈ G) by Tautology.from(invMem of x, xInG)

    val assoc = have(Defs.associative(G)(mul)) by Tautology.from(assoc_of_group, grp)
    thenHave(
      forall(
        x,
        (x ∈ G) ==>
          forall(y, (y ∈ G) ==> forall(z, (z ∈ G) ==> (((x * y) * z) === (x * (y * z)))))
      )
    ) by Substitute(Defs.associative.definition of (G := G, mul := mul))
    val assocUnfolded = lastStep

    val leftInv = have(forall(x, x ∈ G ==> ((x.invOf * x) === one))) by Tautology.from(left_inv_of_group, grp)
    val invMulEqOne = have((x.invOf * x) === one) by Tautology.from(leftInv of x, xInG)

    val assocEq = have(((x.invOf * x) * y) === (x.invOf * (x * y))) by Tautology.from(
      {
        val stepA = have((x.invOf ∈ G) ==> forall(y, (y ∈ G) ==> forall(z, (z ∈ G) ==> (((x.invOf * y) * z) === (x.invOf * (y * z)))))) by Weakening(
          assocUnfolded of x.invOf
        )
        val stepB = have(forall(y, (y ∈ G) ==> forall(z, (z ∈ G) ==> (((x.invOf * y) * z) === (x.invOf * (y * z)))))) by Tautology.from(stepA, invxInG)
        val stepC = have((x ∈ G) ==> forall(z, (z ∈ G) ==> (((x.invOf * x) * z) === (x.invOf * (x * z))))) by Tautology.from(stepB of x)
        val stepD = have(forall(z, (z ∈ G) ==> (((x.invOf * x) * z) === (x.invOf * (x * z))))) by Tautology.from(stepC, xInG)
        val stepE = have((y ∈ G) ==> (((x.invOf * x) * y) === (x.invOf * (x * y)))) by Tautology.from(stepD of y)
        have(((x.invOf * x) * y) === (x.invOf * (x * y))) by Tautology.from(stepE, yInG)
      }
    )
    val assocEqSymm = have((x.invOf * (x * y)) === ((x.invOf * x) * y)) by Tautology.from(assocEq)

    val step2 = have(((x.invOf * x) * y) === (one * y)) by Congruence.from(invMulEqOne)

    val leftId = have(forall(x, x ∈ G ==> ((one * x) === x))) by Tautology.from(left_id_of_group, grp)
    val step3 = have((one * y) === y) by Tautology.from(leftId of y, yInG)

    have(thesis) by Congruence.from(assocEqSymm, step2, step3)
  }

  val mul_inv_cancel_right = Theorem(
    (group(G)(mul)(one)(inv), x ∈ G, y ∈ G) |- (((x * y) * y.invOf) === x)
  ) {
    val grp = assume(group(G)(mul)(one)(inv))
    val xInG = assume(x ∈ G)
    val yInG = assume(y ∈ G)

    val invMem = have(forall(y, y ∈ G ==> (y.invOf ∈ G))) by Tautology.from(inv_mem_of_group, grp)
    val invyInG = have(y.invOf ∈ G) by Tautology.from(invMem of y, yInG)

    val assoc = have(Defs.associative(G)(mul)) by Tautology.from(assoc_of_group, grp)
    thenHave(
      forall(
        x,
        (x ∈ G) ==>
          forall(y, (y ∈ G) ==> forall(z, (z ∈ G) ==> (((x * y) * z) === (x * (y * z)))))
      )
    ) by Substitute(Defs.associative.definition of (G := G, mul := mul))
    val assocUnfolded = lastStep

    val rightInv = have(forall(y, y ∈ G ==> ((y * y.invOf) === one))) by Tautology.from(right_inv_of_group, grp)
    val mulInvEqOne = have((y * y.invOf) === one) by Tautology.from(rightInv of y, yInG)

    val assocEq = have(((x * y) * y.invOf) === (x * (y * y.invOf))) by Tautology.from(
      {
        val stepA = have((x ∈ G) ==> forall(y, (y ∈ G) ==> forall(z, (z ∈ G) ==> (((x * y) * z) === (x * (y * z)))))) by Weakening(
          assocUnfolded of x
        )
        val stepB = have(forall(y, (y ∈ G) ==> forall(z, (z ∈ G) ==> (((x * y) * z) === (x * (y * z)))))) by Tautology.from(stepA, xInG)
        val stepC = have((y ∈ G) ==> forall(z, (z ∈ G) ==> (((x * y) * z) === (x * (y * z))))) by Tautology.from(stepB of y)
        val stepD = have(forall(z, (z ∈ G) ==> (((x * y) * z) === (x * (y * z))))) by Tautology.from(stepC, yInG)
        val stepE = have((y.invOf ∈ G) ==> (((x * y) * y.invOf) === (x * (y * y.invOf)))) by Tautology.from(stepD of y.invOf)
        have(((x * y) * y.invOf) === (x * (y * y.invOf))) by Tautology.from(stepE, invyInG)
      }
    )
    val step2 = have((x * (y * y.invOf)) === (x * one)) by Congruence.from(mulInvEqOne)

    val rightId = have(forall(x, x ∈ G ==> ((x * one) === x))) by Tautology.from(right_id_of_group, grp)
    val step3 = have((x * one) === x) by Tautology.from(rightId of x, xInG)

    have(thesis) by Congruence.from(assocEq, step2, step3)
  }

  val mul_left_cancel_of_group = Theorem(
    (group(G)(mul)(one)(inv), x ∈ G, y ∈ G, z ∈ G, (x * y) === (x * z)) |- y === z
  ) {
    val grp = assume(group(G)(mul)(one)(inv))
    val xInG = assume(x ∈ G)
    val yInG = assume(y ∈ G)
    val zInG = assume(z ∈ G)
    val h = assume((x * y) === (x * z))

    val step0 = have((x.invOf * (x * y)) === (x.invOf * (x * z))) by Congruence.from(h)
    val simpL = have((x.invOf * (x * y)) === y) by Tautology.from(inv_mul_cancel_left, grp, xInG, yInG)
    val simpR = have((x.invOf * (x * z)) === z) by Tautology.from(inv_mul_cancel_left of (y := z), grp, xInG, zInG)

    have(thesis) by Congruence.from(simpL, step0, simpR)
  }

  val mul_right_cancel_of_group = Theorem(
    (group(G)(mul)(one)(inv), x ∈ G, y ∈ G, z ∈ G, (y * x) === (z * x)) |- y === z
  ) {
    val grp = assume(group(G)(mul)(one)(inv))
    val xInG = assume(x ∈ G)
    val yInG = assume(y ∈ G)
    val zInG = assume(z ∈ G)
    val h = assume((y * x) === (z * x))

    val step0 = have(((y * x) * x.invOf) === ((z * x) * x.invOf)) by Congruence.from(h)
    val simpL = have(((y * x) * x.invOf) === y) by Tautology.from(
      mul_inv_cancel_right of (x := y, y := x),
      grp,
      yInG,
      xInG
    )
    val simpR = have(((z * x) * x.invOf) === z) by Tautology.from(
      mul_inv_cancel_right of (x := z, y := x),
      grp,
      zInG,
      xInG
    )

    have(thesis) by Congruence.from(simpL, step0, simpR)
  }

  val mul_eq_one_iff_eq_inv = Theorem(
    (group(G)(mul)(one)(inv), x ∈ G, y ∈ G, (x * y) === one) |- y === x.invOf
  ) {
    val grp = assume(group(G)(mul)(one)(inv))
    val xInG = assume(x ∈ G)
    val yInG = assume(y ∈ G)
    val h = assume((x * y) === one)

    val step0 = have((x.invOf * (x * y)) === (x.invOf * one)) by Congruence.from(h)
    val simpL = have((x.invOf * (x * y)) === y) by Tautology.from(inv_mul_cancel_left, grp, xInG, yInG)

    val invMem = have(forall(x, x ∈ G ==> (x.invOf ∈ G))) by Tautology.from(inv_mem_of_group, grp)
    val invxInG = have(x.invOf ∈ G) by Tautology.from(invMem of x, xInG)

    val rightId = have(forall(x, x ∈ G ==> ((x * one) === x))) by Tautology.from(right_id_of_group, grp)
    val simpR = have((x.invOf * one) === x.invOf) by Tautology.from(rightId of x.invOf, invxInG)

    have(thesis) by Congruence.from(simpL, step0, simpR)
  }

  val identity_unique = Theorem(
    (monoid(G)(mul)(one), monoid(G)(mul)(x)) |- (one === x)
  ) {
    val m1 = assume(monoid(G)(mul)(one))
    val m2 = assume(monoid(G)(mul)(x))

    val `one ∈ G` = have(one ∈ G) by Tautology.from(m1, one_mem_of_monoid)
    val `x ∈ G` = have(x ∈ G) by Tautology.from(m2, one_mem_of_monoid of (one := x))

    have(forall(y, (y ∈ G) ==> (((one * y) === y)))) by Tautology.from(m1, left_id_of_monoid)
    val leftId1 = lastStep
    have(forall(y, (y ∈ G) ==> (((y * one) === y)))) by Tautology.from(m1, right_id_of_monoid)
    val rightId1 = lastStep

    have(forall(y, (y ∈ G) ==> (((x * y) === y)))) by Tautology.from(m2, left_id_of_monoid of (one := x))
    val leftId2 = lastStep
    have(forall(y, (y ∈ G) ==> (((y * x) === y)))) by Tautology.from(m2, right_id_of_monoid of (one := x))
    val rightId2 = lastStep

    import MonoidLike.{e1, e2}
    have(thesis) by Tautology.from(
      MonoidLike.identity_unique of (G := G, mul := mul, e1 := one, e2 := x),
      `one ∈ G`,
      `x ∈ G`,
      leftId1,
      rightId1,
      leftId2,
      rightId2
    )
  }
}
