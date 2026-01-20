package lisa.maths.MathlibPort.Algebra.Ring.Semiring

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Set-based semiring-like predicates (fragment).
 *
 * Lean source reference: `Mathlib/Algebra/Ring/Defs` (semiring portion).
 */
object Defs extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  private val x0 = variable[Ind]

  private def mulApp(mul: Expr[Ind], a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  val mulZero = DEF(λ(R, λ(mul, λ(zero, forall(x0, (x0 ∈ R) ==> (mulApp(mul, x0, zero) === zero))))))
  val zeroMul = DEF(λ(R, λ(mul, λ(zero, forall(x0, (x0 ∈ R) ==> (mulApp(mul, zero, x0) === zero))))))

  val semiring = DEF(
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
              RingDefs.addCommMonoid(R)(add)(zero) /\ RingDefs.mulMonoid(R)(mul)(one) /\ RingDefs.distrib(R)(add)(mul) /\
                mulZero(R)(mul)(zero) /\ zeroMul(R)(mul)(zero)
            )
          )
        )
      )
    )
  )

  val commSemiring = DEF(
    λ(R, λ(add, λ(zero, λ(mul, λ(one, semiring(R)(add)(zero)(mul)(one) /\ RingDefs.commutativeMul(R)(mul))))))
  )
}
