package lisa.maths.SetTheory.Functions

import lisa.maths.SetTheory.Base.Predef.{*, given}
import Function.*
import Sigma.*

/**
 * Given a set `A` and a function `B`, the dependent product `Π(A, B)` is the set
 * of all functions `f ⊆ Σ(A, B)` on `A`.
 */
object Pi extends lisa.Main {

  private val x = variable[Ind]
  private val f = variable[Ind]
  private val A, B = variable[Ind]

  extension (f: Expr[Ind]) {
    def apply(x: Expr[Ind]) = app(f)(x)
  }

  /**
   * Definition --- Given a set `A` and a function `B`, the dependent product
   * `Π(A, B)` is the set of all functions `g ⊆ Σ(A, B)`.
   *
   *    `Π(A, B) = {f ⊆ Σ(A, B) | functionOn(f, A) }`
   */
  val Π = DEF(λ(A, λ(B, { f ⊆ Σ(A)(B) | functionOn(f)(A) })))

  /**
   * Theorem --- The dependent product on the empty set is ∅.
   */
  val emptySet = Theorem(
    Π(∅)(B) === ∅
  ) {
    sorry
  }

}
