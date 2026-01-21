package lisa.maths.MathlibPort.Algebra.Ring.Semiring.Subsemiring

import lisa.maths.SetTheory.Base.Intersection
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Ring/Subsemiring` (basic fragment).
 */
object BasicTheorems extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val S = variable[Ind]
  val T0 = variable[Ind]

  private val x0 = variable[Ind]
  private val y0 = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  val mem_intersection_iff = Theorem(
    x0 ∈ (S ∩ T0) <=> (x0 ∈ S) /\ (x0 ∈ T0)
  ) {
    have(thesis) by Tautology.from(Intersection.membership of (x := S, y := T0, z := x0))
  }

  val subsemiring_intersection = Theorem(
    (Defs.subsemiring(R)(add)(zero)(mul)(one)(S), Defs.subsemiring(R)(add)(zero)(mul)(one)(T0)) |- Defs.subsemiring(R)(add)(zero)(mul)(one)(S ∩ T0)
  ) {
    assume(Defs.subsemiring(R)(add)(zero)(mul)(one)(S))
    thenHave((S ⊆ R) /\ (zero ∈ S) /\ (one ∈ S) /\ Defs.closedAdd(add)(S) /\ Defs.closedMul(mul)(S)) by Substitute(
      Defs.subsemiring.definition of (Defs.R := R, Defs.add := add, Defs.zero := zero, Defs.mul := mul, Defs.one := one, Defs.S := S)
    )
    val sData = lastStep

    assume(Defs.subsemiring(R)(add)(zero)(mul)(one)(T0))
    thenHave((T0 ⊆ R) /\ (zero ∈ T0) /\ (one ∈ T0) /\ Defs.closedAdd(add)(T0) /\ Defs.closedMul(mul)(T0)) by Substitute(
      Defs.subsemiring.definition of (Defs.R := R, Defs.add := add, Defs.zero := zero, Defs.mul := mul, Defs.one := one, Defs.S := T0)
    )
    val tData = lastStep

    have((S ∩ T0) ⊆ R) by Tautology.from(
      Subset.transitivity of (x := (S ∩ T0), y := S, z := R),
      Intersection.subsetLeft of (x := S, y := T0),
      sData
    )
    val stSubset = lastStep

    have(zero ∈ (S ∩ T0)) by Tautology.from(
      mem_intersection_iff of (x0 := zero, S := S, T0 := T0),
      sData,
      tData
    )
    val stZero = lastStep

    have(one ∈ (S ∩ T0)) by Tautology.from(
      mem_intersection_iff of (x0 := one, S := S, T0 := T0),
      sData,
      tData
    )
    val stOne = lastStep

    val sClosedAdd = have(forall(x0, (x0 ∈ S) ==> forall(y0, (y0 ∈ S) ==> (addApp(x0, y0) ∈ S)))) by Tautology.from(
      sData,
      Defs.closedAdd.definition of (Defs.add := add, Defs.S := S)
    )
    val tClosedAdd = have(forall(x0, (x0 ∈ T0) ==> forall(y0, (y0 ∈ T0) ==> (addApp(x0, y0) ∈ T0)))) by Tautology.from(
      tData,
      Defs.closedAdd.definition of (Defs.add := add, Defs.S := T0)
    )

    val sClosedMul = have(forall(x0, (x0 ∈ S) ==> forall(y0, (y0 ∈ S) ==> (mulApp(x0, y0) ∈ S)))) by Tautology.from(
      sData,
      Defs.closedMul.definition of (Defs.mul := mul, Defs.S := S)
    )
    val tClosedMul = have(forall(x0, (x0 ∈ T0) ==> forall(y0, (y0 ∈ T0) ==> (mulApp(x0, y0) ∈ T0)))) by Tautology.from(
      tData,
      Defs.closedMul.definition of (Defs.mul := mul, Defs.S := T0)
    )

    have(Defs.closedAdd(add)(S ∩ T0)) subproof {
      have(forall(x0, (x0 ∈ (S ∩ T0)) ==> forall(y0, (y0 ∈ (S ∩ T0)) ==> (addApp(x0, y0) ∈ (S ∩ T0))))) subproof {
        have((x0 ∈ (S ∩ T0)) ==> forall(y0, (y0 ∈ (S ∩ T0)) ==> (addApp(x0, y0) ∈ (S ∩ T0)))) subproof {
          val xInST = assume(x0 ∈ (S ∩ T0))
          val xInBoth = have((x0 ∈ S) /\ (x0 ∈ T0)) by Tautology.from(mem_intersection_iff of (x0 := x0, S := S, T0 := T0), xInST)
          val xInS = have(x0 ∈ S) by Tautology.from(xInBoth)
          val xInT = have(x0 ∈ T0) by Tautology.from(xInBoth)

          have(forall(y0, (y0 ∈ (S ∩ T0)) ==> (addApp(x0, y0) ∈ (S ∩ T0)))) subproof {
            have((y0 ∈ (S ∩ T0)) ==> (addApp(x0, y0) ∈ (S ∩ T0))) subproof {
              val yInST = assume(y0 ∈ (S ∩ T0))
              val yInBoth = have((y0 ∈ S) /\ (y0 ∈ T0)) by Tautology.from(mem_intersection_iff of (x0 := y0, S := S, T0 := T0), yInST)
              val yInS = have(y0 ∈ S) by Tautology.from(yInBoth)
              val yInT = have(y0 ∈ T0) by Tautology.from(yInBoth)

              val sAtX = have(forall(y0, (y0 ∈ S) ==> (addApp(x0, y0) ∈ S))) by Tautology.from(sClosedAdd of x0, xInS)
              val xyInS = have(addApp(x0, y0) ∈ S) by Tautology.from(sAtX of y0, yInS)

              val tAtX = have(forall(y0, (y0 ∈ T0) ==> (addApp(x0, y0) ∈ T0))) by Tautology.from(tClosedAdd of x0, xInT)
              val xyInT = have(addApp(x0, y0) ∈ T0) by Tautology.from(tAtX of y0, yInT)

              have(addApp(x0, y0) ∈ (S ∩ T0)) by Tautology.from(
                mem_intersection_iff of (x0 := addApp(x0, y0), S := S, T0 := T0),
                xyInS,
                xyInT
              )
              thenHave(thesis) by RightImplies.withParameters(
                y0 ∈ (S ∩ T0),
                addApp(x0, y0) ∈ (S ∩ T0)
              )
            }
            thenHave(thesis) by RightForall.withParameters((y0 ∈ (S ∩ T0)) ==> (addApp(x0, y0) ∈ (S ∩ T0)), y0)
          }

          thenHave(thesis) by RightImplies.withParameters(
            x0 ∈ (S ∩ T0),
            forall(y0, (y0 ∈ (S ∩ T0)) ==> (addApp(x0, y0) ∈ (S ∩ T0)))
          )
        }
        thenHave(thesis) by RightForall.withParameters(
          (x0 ∈ (S ∩ T0)) ==> forall(y0, (y0 ∈ (S ∩ T0)) ==> (addApp(x0, y0) ∈ (S ∩ T0))),
          x0
        )
      }
      thenHave(thesis) by Substitute(Defs.closedAdd.definition of (Defs.add := add, Defs.S := (S ∩ T0)))
    }
    val stClosedAdd = lastStep

    have(Defs.closedMul(mul)(S ∩ T0)) subproof {
      have(forall(x0, (x0 ∈ (S ∩ T0)) ==> forall(y0, (y0 ∈ (S ∩ T0)) ==> (mulApp(x0, y0) ∈ (S ∩ T0))))) subproof {
        have((x0 ∈ (S ∩ T0)) ==> forall(y0, (y0 ∈ (S ∩ T0)) ==> (mulApp(x0, y0) ∈ (S ∩ T0)))) subproof {
          val xInST = assume(x0 ∈ (S ∩ T0))
          val xInBoth = have((x0 ∈ S) /\ (x0 ∈ T0)) by Tautology.from(mem_intersection_iff of (x0 := x0, S := S, T0 := T0), xInST)
          val xInS = have(x0 ∈ S) by Tautology.from(xInBoth)
          val xInT = have(x0 ∈ T0) by Tautology.from(xInBoth)

          have(forall(y0, (y0 ∈ (S ∩ T0)) ==> (mulApp(x0, y0) ∈ (S ∩ T0)))) subproof {
            have((y0 ∈ (S ∩ T0)) ==> (mulApp(x0, y0) ∈ (S ∩ T0))) subproof {
              val yInST = assume(y0 ∈ (S ∩ T0))
              val yInBoth = have((y0 ∈ S) /\ (y0 ∈ T0)) by Tautology.from(mem_intersection_iff of (x0 := y0, S := S, T0 := T0), yInST)
              val yInS = have(y0 ∈ S) by Tautology.from(yInBoth)
              val yInT = have(y0 ∈ T0) by Tautology.from(yInBoth)

              val sAtX = have(forall(y0, (y0 ∈ S) ==> (mulApp(x0, y0) ∈ S))) by Tautology.from(sClosedMul of x0, xInS)
              val xyInS = have(mulApp(x0, y0) ∈ S) by Tautology.from(sAtX of y0, yInS)

              val tAtX = have(forall(y0, (y0 ∈ T0) ==> (mulApp(x0, y0) ∈ T0))) by Tautology.from(tClosedMul of x0, xInT)
              val xyInT = have(mulApp(x0, y0) ∈ T0) by Tautology.from(tAtX of y0, yInT)

              have(mulApp(x0, y0) ∈ (S ∩ T0)) by Tautology.from(
                mem_intersection_iff of (x0 := mulApp(x0, y0), S := S, T0 := T0),
                xyInS,
                xyInT
              )
              thenHave(thesis) by RightImplies.withParameters(
                y0 ∈ (S ∩ T0),
                mulApp(x0, y0) ∈ (S ∩ T0)
              )
            }
            thenHave(thesis) by RightForall.withParameters((y0 ∈ (S ∩ T0)) ==> (mulApp(x0, y0) ∈ (S ∩ T0)), y0)
          }

          thenHave(thesis) by RightImplies.withParameters(
            x0 ∈ (S ∩ T0),
            forall(y0, (y0 ∈ (S ∩ T0)) ==> (mulApp(x0, y0) ∈ (S ∩ T0)))
          )
        }
        thenHave(thesis) by RightForall.withParameters(
          (x0 ∈ (S ∩ T0)) ==> forall(y0, (y0 ∈ (S ∩ T0)) ==> (mulApp(x0, y0) ∈ (S ∩ T0))),
          x0
        )
      }
      thenHave(thesis) by Substitute(Defs.closedMul.definition of (Defs.mul := mul, Defs.S := (S ∩ T0)))
    }
    val stClosedMul = lastStep

    have(thesis) by Tautology.from(
      Defs.subsemiring.definition of (Defs.R := R, Defs.add := add, Defs.zero := zero, Defs.mul := mul, Defs.one := one, Defs.S := (S ∩ T0)),
      stSubset,
      stZero,
      stOne,
      stClosedAdd,
      stClosedMul
    )
  }
}
