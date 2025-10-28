package lisa.maths.SetTheory.Functions

import lisa.maths.SetTheory.Base.Predef.{*, given}
import Function.*

/**
 * Given a set `A` and a function `B`, the dependent sum `Σ(A, B)` is the set
 * of all pairs `(a, b)` such that `a ∈ A` and `b ∈ B(a)`.
 */
object Sigma extends lisa.Main {

  private val x = variable[Ind]
  private val a, b = variable[Ind]
  private val A = variable[Ind]
  private val B = variable[Ind]

  extension (f: Expr[Ind]) {
    def apply(x: Expr[Ind]) = app(f)(x)
  }

  /**
   * Definition --- Given a set `A` and a function `B`, the dependent sum `Σ(A, B)`
   * is the set of all pairs `(a, b)` such that `a ∈ A` and `b ∈ B(a)`.
   *
   *    `Σ(A, B) = {(a, b) | a ∈ A, b ∈ B(a) }`
   */
  val Σ = DEF(λ(A, λ(B, { x ∈ (A × { B(a) | a ∈ A }) | snd(x) ∈ B(fst(x)) })))

  /**
   * Theorem --- The dependent sum on the empty set is ∅.
   */
  val emptySet = Theorem(
    Σ(∅)(B) === ∅
  ) {
    sorry
  }

  /**
   * Theorem --- We have `(a, b) ∈ Σ(A, B)` <=> `a ∈ A` and `b ∈ B(a)`.
   */
  val membership = Theorem(
    (a, b) ∈ Σ(A)(B) <=> (a ∈ A) /\ (b ∈ B(a))
  ) {
    sorry
  }

}
