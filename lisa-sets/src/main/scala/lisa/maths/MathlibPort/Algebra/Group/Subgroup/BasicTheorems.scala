package lisa.maths.MathlibPort.Algebra.Group.Subgroup

import lisa.maths.SetTheory.Base.Intersection
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/GroupTheory/Subgroup/Basic` (basic theorems fragment).
 */
object BasicTheorems extends lisa.Main {

  val G = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]
  val inv = variable[Ind]

  val H = variable[Ind]
  val K0 = variable[Ind]

  private val x0 = variable[Ind]
  private val y0 = variable[Ind]

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  private def invApp(a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(inv)(a)

  val mem_intersection_iff = Theorem(
    x0 ∈ (H ∩ K0) <=> (x0 ∈ H) /\ (x0 ∈ K0)
  ) {
    have(thesis) by Tautology.from(Intersection.membership of (x := H, y := K0, z := x0))
  }

  val one_mem_intersection = Theorem(
    (one ∈ H, one ∈ K0) |- one ∈ (H ∩ K0)
  ) {
    have(thesis) by Tautology.from(mem_intersection_iff of (x0 := one, H := H, K0 := K0))
  }

  val closedMul_intersection = Theorem(
    (Defs.closedMul(mul)(H), Defs.closedMul(mul)(K0)) |- Defs.closedMul(mul)(H ∩ K0)
  ) {
    assume(Defs.closedMul(mul)(H))
    thenHave(forall(x0, (x0 ∈ H) ==> forall(y0, (y0 ∈ H) ==> (mulApp(x0, y0) ∈ H)))) by Substitute(
      Defs.closedMul.definition of (mul := mul, H := H)
    )
    val closedH = lastStep

    assume(Defs.closedMul(mul)(K0))
    thenHave(forall(x0, (x0 ∈ K0) ==> forall(y0, (y0 ∈ K0) ==> (mulApp(x0, y0) ∈ K0)))) by Substitute(
      Defs.closedMul.definition of (mul := mul, H := K0)
    )
    val closedK = lastStep

    // Build the defining property of `closedMul(H ∩ K0)` and rewrite back via the definition.
    have(forall(x0, (x0 ∈ (H ∩ K0)) ==> forall(y0, (y0 ∈ (H ∩ K0)) ==> (mulApp(x0, y0) ∈ (H ∩ K0))))) subproof {
      have((x0 ∈ (H ∩ K0)) ==> forall(y0, (y0 ∈ (H ∩ K0)) ==> (mulApp(x0, y0) ∈ (H ∩ K0)))) subproof {
        val xInHK0 = assume(x0 ∈ (H ∩ K0))
        val xInHK = have((x0 ∈ H) /\ (x0 ∈ K0)) by Tautology.from(
          mem_intersection_iff of (x0 := x0, H := H, K0 := K0),
          xInHK0
        )
        val xInH = have(x0 ∈ H) by Tautology.from(xInHK)
        val xInK = have(x0 ∈ K0) by Tautology.from(xInHK)

        have(forall(y0, (y0 ∈ (H ∩ K0)) ==> (mulApp(x0, y0) ∈ (H ∩ K0)))) subproof {
          have((y0 ∈ (H ∩ K0)) ==> (mulApp(x0, y0) ∈ (H ∩ K0))) subproof {
            val yInHK0 = assume(y0 ∈ (H ∩ K0))
            val yInHK = have((y0 ∈ H) /\ (y0 ∈ K0)) by Tautology.from(
              mem_intersection_iff of (x0 := y0, H := H, K0 := K0),
              yInHK0
            )
            val yInH = have(y0 ∈ H) by Tautology.from(yInHK)
            val yInK = have(y0 ∈ K0) by Tautology.from(yInHK)

            val closedHAtX = have(forall(y0, (y0 ∈ H) ==> (mulApp(x0, y0) ∈ H))) by Tautology.from(closedH of x0, xInH)
            val xyInH = have(mulApp(x0, y0) ∈ H) by Tautology.from(closedHAtX of y0, yInH)

            val closedKAtX = have(forall(y0, (y0 ∈ K0) ==> (mulApp(x0, y0) ∈ K0))) by Tautology.from(closedK of x0, xInK)
            val xyInK = have(mulApp(x0, y0) ∈ K0) by Tautology.from(closedKAtX of y0, yInK)

            have(mulApp(x0, y0) ∈ (H ∩ K0)) by Tautology.from(
              mem_intersection_iff of (x0 := mulApp(x0, y0), H := H, K0 := K0),
              xyInH,
              xyInK
            )
            thenHave(thesis) by RightImplies.withParameters(
              y0 ∈ (H ∩ K0),
              mulApp(x0, y0) ∈ (H ∩ K0)
            )
          }

          thenHave(thesis) by RightForall.withParameters(
            (y0 ∈ (H ∩ K0)) ==> (mulApp(x0, y0) ∈ (H ∩ K0)),
            y0
          )
        }

        thenHave(thesis) by RightImplies.withParameters(
          x0 ∈ (H ∩ K0),
          forall(y0, (y0 ∈ (H ∩ K0)) ==> (mulApp(x0, y0) ∈ (H ∩ K0)))
        )
      }

      thenHave(thesis) by RightForall.withParameters(
        (x0 ∈ (H ∩ K0)) ==> forall(y0, (y0 ∈ (H ∩ K0)) ==> (mulApp(x0, y0) ∈ (H ∩ K0))),
        x0
      )
    }

    thenHave(thesis) by Substitute(Defs.closedMul.definition of (mul := mul, H := (H ∩ K0)))
  }

  val closedInv_intersection = Theorem(
    (Defs.closedInv(inv)(H), Defs.closedInv(inv)(K0)) |- Defs.closedInv(inv)(H ∩ K0)
  ) {
    assume(Defs.closedInv(inv)(H))
    thenHave(forall(x0, (x0 ∈ H) ==> (invApp(x0) ∈ H))) by Substitute(Defs.closedInv.definition of (inv := inv, H := H))
    val closedH = lastStep

    assume(Defs.closedInv(inv)(K0))
    thenHave(forall(x0, (x0 ∈ K0) ==> (invApp(x0) ∈ K0))) by Substitute(Defs.closedInv.definition of (inv := inv, H := K0))
    val closedK = lastStep

    have(forall(x0, (x0 ∈ (H ∩ K0)) ==> (invApp(x0) ∈ (H ∩ K0)))) subproof {
      have((x0 ∈ (H ∩ K0)) ==> (invApp(x0) ∈ (H ∩ K0))) subproof {
        val xInHK0 = assume(x0 ∈ (H ∩ K0))
        val xInHK = have((x0 ∈ H) /\ (x0 ∈ K0)) by Tautology.from(
          mem_intersection_iff of (x0 := x0, H := H, K0 := K0),
          xInHK0
        )
        val xInH = have(x0 ∈ H) by Tautology.from(xInHK)
        val xInK = have(x0 ∈ K0) by Tautology.from(xInHK)

        val invInH = have(invApp(x0) ∈ H) by Tautology.from(closedH of x0, xInH)
        val invInK = have(invApp(x0) ∈ K0) by Tautology.from(closedK of x0, xInK)
        have(invApp(x0) ∈ (H ∩ K0)) by Tautology.from(
          mem_intersection_iff of (x0 := invApp(x0), H := H, K0 := K0),
          invInH,
          invInK
        )

        thenHave(thesis) by RightImplies.withParameters(
          x0 ∈ (H ∩ K0),
          invApp(x0) ∈ (H ∩ K0)
        )
      }

      thenHave(thesis) by RightForall.withParameters(
        (x0 ∈ (H ∩ K0)) ==> (invApp(x0) ∈ (H ∩ K0)),
        x0
      )
    }
    thenHave(thesis) by Substitute(Defs.closedInv.definition of (inv := inv, H := (H ∩ K0)))
  }

  val subgroup_intersection = Theorem(
    (Defs.subgroup(G)(mul)(one)(inv)(H), Defs.subgroup(G)(mul)(one)(inv)(K0)) |- Defs.subgroup(G)(mul)(one)(inv)(H ∩ K0)
  ) {
    assume(Defs.subgroup(G)(mul)(one)(inv)(H))
    thenHave(H ⊆ G /\ (one ∈ H) /\ Defs.closedMul(mul)(H) /\ Defs.closedInv(inv)(H)) by Substitute(
      Defs.subgroup.definition of (H := H, mul := mul, inv := inv)
    )
    val hData = lastStep

    assume(Defs.subgroup(G)(mul)(one)(inv)(K0))
    thenHave(K0 ⊆ G /\ (one ∈ K0) /\ Defs.closedMul(mul)(K0) /\ Defs.closedInv(inv)(K0)) by Substitute(
      Defs.subgroup.definition of (H := K0, mul := mul, inv := inv)
    )
    val kData = lastStep

    have((H ∩ K0) ⊆ G) by Tautology.from(
      Subset.transitivity of (x := (H ∩ K0), y := H, z := G),
      Intersection.subsetLeft of (x := H, y := K0),
      hData
    )
    val hkSubset = lastStep

    have(one ∈ (H ∩ K0)) by Tautology.from(one_mem_intersection, hData, kData)
    val hkOne = lastStep

    have(Defs.closedMul(mul)(H ∩ K0)) by Tautology.from(closedMul_intersection, hData, kData)
    val hkMul = lastStep

    have(Defs.closedInv(inv)(H ∩ K0)) by Tautology.from(closedInv_intersection, hData, kData)
    val hkInv = lastStep

    have(
      (H ∩ K0) ⊆ G /\ (one ∈ (H ∩ K0)) /\ Defs.closedMul(mul)(H ∩ K0) /\ Defs.closedInv(inv)(H ∩ K0)
    ) by Tautology.from(
      hkSubset,
      hkOne,
      hkMul,
      hkInv
    )
    thenHave(thesis) by Substitute(Defs.subgroup.definition of (H := (H ∩ K0), mul := mul, inv := inv))
  }

  val subset_of_subgroup = Theorem(
    Defs.subgroup(G)(mul)(one)(inv)(H) |- H ⊆ G
  ) {
    have(thesis) by Tautology.from(Defs.subgroup.definition)
  }

  val one_mem_of_subgroup = Theorem(
    Defs.subgroup(G)(mul)(one)(inv)(H) |- one ∈ H
  ) {
    have(thesis) by Tautology.from(Defs.subgroup.definition)
  }

  val closedMul_of_subgroup = Theorem(
    Defs.subgroup(G)(mul)(one)(inv)(H) |- Defs.closedMul(mul)(H)
  ) {
    have(thesis) by Tautology.from(Defs.subgroup.definition)
  }

  val closedInv_of_subgroup = Theorem(
    Defs.subgroup(G)(mul)(one)(inv)(H) |- Defs.closedInv(inv)(H)
  ) {
    have(thesis) by Tautology.from(Defs.subgroup.definition)
  }

  val mul_mem_of_closedMul = Theorem(
    (Defs.closedMul(mul)(H), x0 ∈ H, y0 ∈ H) |- mulApp(x0, y0) ∈ H
  ) {
    val closed = assume(Defs.closedMul(mul)(H))
    thenHave(forall(x0, (x0 ∈ H) ==> forall(y0, (y0 ∈ H) ==> (mulApp(x0, y0) ∈ H)))) by Substitute(
      Defs.closedMul.definition of (mul := mul, H := H)
    )
    val closedUnfolded = lastStep

    val xInH = assume(x0 ∈ H)
    val yInH = assume(y0 ∈ H)

    val closedAtX = have(forall(y0, (y0 ∈ H) ==> (mulApp(x0, y0) ∈ H))) by Tautology.from(closedUnfolded of x0, xInH)
    have(thesis) by Tautology.from(closedAtX of y0, yInH)
  }

  val inv_mem_of_closedInv = Theorem(
    (Defs.closedInv(inv)(H), x0 ∈ H) |- invApp(x0) ∈ H
  ) {
    val closed = assume(Defs.closedInv(inv)(H))
    thenHave(forall(x0, (x0 ∈ H) ==> (invApp(x0) ∈ H))) by Substitute(
      Defs.closedInv.definition of (inv := inv, H := H)
    )
    val closedUnfolded = lastStep

    val xInH = assume(x0 ∈ H)
    have(thesis) by Tautology.from(closedUnfolded of x0, xInH)
  }

  val mul_mem_of_subgroup = Theorem(
    (Defs.subgroup(G)(mul)(one)(inv)(H), x0 ∈ H, y0 ∈ H) |- mulApp(x0, y0) ∈ H
  ) {
    val subH = assume(Defs.subgroup(G)(mul)(one)(inv)(H))
    val xInH = assume(x0 ∈ H)
    val yInH = assume(y0 ∈ H)

    have(Defs.closedMul(mul)(H)) by Tautology.from(closedMul_of_subgroup, subH)
    have(thesis) by Tautology.from(mul_mem_of_closedMul, lastStep, xInH, yInH)
  }

  val inv_mem_of_subgroup = Theorem(
    (Defs.subgroup(G)(mul)(one)(inv)(H), x0 ∈ H) |- invApp(x0) ∈ H
  ) {
    val subH = assume(Defs.subgroup(G)(mul)(one)(inv)(H))
    val xInH = assume(x0 ∈ H)

    have(Defs.closedInv(inv)(H)) by Tautology.from(closedInv_of_subgroup, subH)
    have(thesis) by Tautology.from(inv_mem_of_closedInv, lastStep, xInH)
  }
}
