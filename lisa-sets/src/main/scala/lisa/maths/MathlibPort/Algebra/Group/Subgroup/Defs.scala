package lisa.maths.MathlibPort.Algebra.Group.Subgroup

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/GroupTheory/Subgroup/Basic` (defs fragment).
 *
 * A subgroup is represented as a subset `H ⊆ G` closed under multiplication and inverse
 * and containing the identity element.
 */
object Defs extends lisa.Main {

  val G = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]
  val inv = variable[Ind]

  val H = variable[Ind]

  private val x0 = variable[Ind]
  private val y0 = variable[Ind]

  private def mulApp(m: Expr[Ind], a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(m)((a, b))

  private def invApp(i: Expr[Ind], a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(i)(a)

  val closedMul = DEF(
    λ(mul, λ(H, forall(x0, (x0 ∈ H) ==> forall(y0, (y0 ∈ H) ==> (mulApp(mul, x0, y0) ∈ H)))))
  )

  val closedInv = DEF(
    λ(inv, λ(H, forall(x0, (x0 ∈ H) ==> (invApp(inv, x0) ∈ H))))
  )

  val subgroup = DEF(
    λ(
      G,
      λ(
        mul,
        λ(
          one,
          λ(inv, λ(H, (H ⊆ G) /\ (one ∈ H) /\ closedMul(mul)(H) /\ closedInv(inv)(H)))
        )
      )
    )
  )
}
