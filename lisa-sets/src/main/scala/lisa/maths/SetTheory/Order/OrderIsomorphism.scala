package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*

/**
 * Two orders `(A, <A)` and `(B, <B)` are isomorphic if there exists a bijection
 * `f : A -> B` such that for all `x, y ∈ A` we have `x <A y` if and only if
 * `f(x) <B f(y)`.
 */
object OrderIsomorphism extends lisa.Main {

  private val `<A`, `<B` = variable[Ind]

  extension (f: Expr[Ind]) {
    private def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * Order isomorphism --- `f` is an order-isomorphism between `(A, <A)` and
   * `(B, <B)` if and only if `f` is bijective and satisfies:
   *
   *   `∀ x, y. x <A y <=> f(x) <B f(y)`
   */
  val isomorphism = DEF(λ(f, λ(A, λ(`<A`, λ(B, λ(`<B`, bijective(f)(A)(B) /\ ∀(x, ∀(y, (x, y) ∈ `<A` <=> (f(x), f(y)) ∈ `<B`))))))))

  /**
   * Order isomorphic --- `(A, <A)` and `(B, <B)` are order-isomorphic if there
   * exists an [[isomorphic]] `f`.
   *
   * @see [[isomorphic]]
   */
  val isomorphic = DEF(λ(A, λ(`<A`, λ(B, λ(`<B`, ∃(f, isomorphism(f)(A)(`<A`)(B)(`<B`))))))).printAs(args => {
    val A = args(0)
    val `<A` = args(1)
    val B = args(2)
    val `<B` = args(3)
    s"($A, ${`<A`}) ≈ ($B, ${`<B`})"
  })

  extension (orderA: (Expr[Ind], Expr[Ind])) {

    /**
     * Notation `(A, <A) ≈ (B, <B)`.
     */
    inline infix def ≈(orderB: (Expr[Ind], Expr[Ind])): Expr[Prop] =
      isomorphic(orderA._1)(orderA._2)(orderB._1)(orderB._2)
  }
}
