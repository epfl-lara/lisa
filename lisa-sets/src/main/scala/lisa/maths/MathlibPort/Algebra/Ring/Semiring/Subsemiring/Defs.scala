package lisa.maths.MathlibPort.Algebra.Ring.Semiring.Subsemiring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Ring/Subsemiring` (defs fragment).
 */
object Defs extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val S = variable[Ind]

  private val x0 = variable[Ind]
  private val y0 = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  val closedAdd = DEF(λ(add, λ(S, forall(x0, (x0 ∈ S) ==> forall(y0, (y0 ∈ S) ==> (addApp(x0, y0) ∈ S))))))
  val closedMul = DEF(λ(mul, λ(S, forall(x0, (x0 ∈ S) ==> forall(y0, (y0 ∈ S) ==> (mulApp(x0, y0) ∈ S))))))

  val subsemiring = DEF(
    λ(
      R,
      λ(
        add,
        λ(
          zero,
          λ(
            mul,
            λ(
              one,
              λ(
                S,
                (S ⊆ R) /\ (zero ∈ S) /\ (one ∈ S) /\ closedAdd(add)(S) /\ closedMul(mul)(S)
              )
            )
          )
        )
      )
    )
  )
}

