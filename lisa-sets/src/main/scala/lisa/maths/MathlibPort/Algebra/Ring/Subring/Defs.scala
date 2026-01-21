package lisa.maths.MathlibPort.Algebra.Ring.Subring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Ring/Subring` (defs fragment).
 */
object Defs extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val S = variable[Ind]

  private val x0 = variable[Ind]
  private val y0 = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def negApp(a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(negOp)(a)

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  val closedAdd = DEF(λ(add, λ(S, forall(x0, (x0 ∈ S) ==> forall(y0, (y0 ∈ S) ==> (addApp(x0, y0) ∈ S))))))
  val closedMul = DEF(λ(mul, λ(S, forall(x0, (x0 ∈ S) ==> forall(y0, (y0 ∈ S) ==> (mulApp(x0, y0) ∈ S))))))
  val closedNeg = DEF(λ(negOp, λ(S, forall(x0, (x0 ∈ S) ==> (negApp(x0) ∈ S)))))

  val subring = DEF(
    λ(
      R,
      λ(
        add,
        λ(
          zero,
          λ(
            negOp,
            λ(
              mul,
              λ(
                one,
                λ(
                  S,
                  (S ⊆ R) /\ (zero ∈ S) /\ (one ∈ S) /\ closedAdd(add)(S) /\ closedNeg(negOp)(S) /\ closedMul(mul)(S)
                )
              )
            )
          )
        )
      )
    )
  )
}

