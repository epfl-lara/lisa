package lisa.maths.SetTheory.Functions

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef.*

import lisa.maths.Quantifiers.∃!

/**
 * A function `f : A -> B` is a relation `f ⊆ A × B` such that for any
 * `x ∈ A` there is a unique `y ∈ B` such that `(x, y) ∈ f`.
 */
object Definitions extends lisa.Main {

  private val x, y = variable[Ind]
  private val f, g = variable[Ind]
  private val A, B = variable[Ind]

  /**
   * Definition --- `f : A -> B` is a function between `A` and `B` if `f ⊆ A × B`
   * such that for all `x ∈ A` there is a unique `y ∈ B` such that `(x, y) ∈ f`.
   */
  val functionBetween = DEF(λ(f, λ(A, λ(B, relationBetween(f)(A)(B) /\ ∀(x, x ∈ A ==> ∃!(y, (x, y) ∈ f))))))

  extension (f: set) {

    /**
     * Notation `f :: A -> B`
     */
    infix def ::(fType: (set, set)): Expr[Prop] =
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
   * @see [[Relations.Definitions.dom]]
   */
  val dom = Relations.Predef.dom

  /**
   * Function range --- The range of `f` is the set of elements that are mapped by one value.
   *
   * @see [[Relations.Definitions.dom]]
   */
  val range = Relations.Predef.range

  /**
   * Function application --- For any `x`, we denote by `f(x)` the application
   * of `f` to `x`.
   *
   * If `x ∉ A`, this value is undefined.
   */
  val app = DEF(λ(f, λ(x, ε(y, (x, y) ∈ f))))

  extension (f: set) {

    /**
     * Syntax for `f(x)`.
     */
    def apply(x: set): set = app(f)(x)
  }

  /**
   * Injective function --- `f : A -> B` is said to be injective on `A` if `f(x) = f(y)` implies `x = y`.
   */
  val injective = DEF(λ(f, λ(A, λ(B, ∀(x, ∀(y, (x ∈ A) /\ (y ∈ A) /\ (f(x) === f(y)) ==> (x === y)))))))
  val oneToOne = injective

  /**
   * Surjective function --- `f : A -> B` is said to be surjective (or onto) if `range(f) = B`.
   */
  val surjective = DEF(λ(f, λ(A, λ(B, (f :: A -> B) /\ (range(f) === B)))))
  val onto = surjective

  /**
   * Bijective function --- `f : A -> B` is said to be bijective if is both injective
   * and surjective.
   */
  val bijective = DEF(λ(f, λ(A, λ(B, injective(f)(A)(B) /\ surjective(f)(A)(B)))))

}
