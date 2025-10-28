package lisa.maths.SetTheory.Functions

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Relation
import lisa.maths.SetTheory.Relations.Predef.*

import lisa.maths.Quantifiers.∃!

import scala.annotation.targetName

/**
 * A function `f : A -> B` is a relation `f ⊆ A × B` such that for any
 * `x ∈ A` there is a unique `y ∈ B` such that `(x, y) ∈ f`.
 */
object Function extends lisa.Main {

  /**
   * Definition --- `f : A -> B` is a function between `A` and `B` if `f ⊆ A × B`
   * such that for all `x ∈ A` there is a unique `y ∈ B` such that `(x, y) ∈ f`.
   */
  val functionBetween = DEF(λ(f, λ(A, λ(B, relationBetween(f)(A)(B) /\ ∀(x ∈ A, ∃!(y, (x, y) ∈ f))))))

  extension (f: Expr[Ind]) {

    /**
     * Notation `f :: A -> B`
     */
    infix def ::(fType: (Expr[Ind], Expr[Ind])): Expr[Prop] =
      val (a, b) = fType
      functionBetween(f)(a)(b)
  }

  /**
   * Definition --- `f` is a function on `A` if the domain of `f` is `A`.
   */
  val functionOn = DEF(λ(f, λ(A, ∃(B, f :: A -> B))))

  /**
   * Definition --- `f` is a function if there exists `A` and `B` such that `f : A -> B`.
   */
  val function = DEF(λ(f, ∃(A, ∃(B, f :: A -> B))))

  /**
   * Function domain --- The domain of `f` is the set of elements that have a mapped value.
   *
   * @see [[Relation.dom]]
   */
  export Relation.dom

  /**
   * Function range --- The range of `f` is the set of elements that are mapped
   * by (at least) one value.
   *
   * @see [[Relation.dom]]
   */
  export Relation.range

  /**
   * Function application --- For any `x`, we denote by `f(x)` the application
   * of `f` to `x`.
   *
   * If `x ∉ A`, this value is undefined.
   */
  val app = DEF(λ(f, λ(x, ε(y, (x, y) ∈ f)))).printAs(args => {
    val f = args(0)
    val x = args(1)
    s"$f($x)"
  })

  extension (f: Expr[Ind]) {
    /** Syntax for `f(x)`. */
    def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * Injective function --- `f` is said to be injective on `A` if `f(x) = f(y)` implies `x = y`.
   */
  val injective = DEF(λ(f, λ(A, ∀(x ∈ A, ∀(y ∈ A, (f(x) === f(y)) ==> (x === y))))))
  inline def oneToOne = injective

  /**
   * Surjective function --- `f` is said to be surjective on (or onto) `B` if `range(f) = B`.
   */
  val surjective = DEF(λ(f, λ(B, range(f) === B)))
  inline def onto = surjective

  /**
   * Bijective function --- `f : A -> B` is said to be bijective if is both injective
   * and surjective.
   */
  val bijective = DEF(λ(f, λ(A, λ(B, (f :: A -> B) /\ injective(f)(A) /\ surjective(f)(B)))))

}
