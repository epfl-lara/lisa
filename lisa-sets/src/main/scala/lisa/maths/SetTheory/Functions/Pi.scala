package lisa.maths.SetTheory.Functions

import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}

import Function.{apply => _, _}
import Sigma._

/**
 * Given a set `A` and a function `B`, the dependent product `Π(A, B)` is the set
 * of all functions `f ⊆ Σ(A, B)` on `A`.
 */
object Pi extends lisa.Main {

  private val x = variable[Ind]
  private val f = variable[Ind]
  private val A, B = variable[Ind]

  private val T, T1, e = variable[Ind]
  private val T2 = variable[Ind >>: Ind]

  extension (f: Expr[Ind]) {
    def apply(x: Expr[Ind]) = app.apply(f)(x)
  }

  /**
   * Definition --- Given a set `A` and a function `B`, the dependent product
   * `Π(A, B)` is the set of all functions `g ⊆ Σ(A, B)`.
   *
   *    `Π(A, B) = {f ⊆ Σ(A, B) | functionOn(f, A) }`
   */
  val Pi: Constant[Ind >>: (Ind >>: Ind) >>: Ind] = DEF(
    λ(
      T1,
      λ(
        T2, {
          f ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 })) |
            // f is a function
            (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\
            // f(a)'s type should be T2(a)
            (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a))))) //
        }
      )
    )
  ).printAs(args =>
    val ty1 = args(0)
    val ty2 = args(1)
    ty2 match
      case Abs(v, body) =>
        if body.freeVars.contains(v) then s"Π($v: $ty1). $body"
        else s"($ty1 ->: $body)"
      case _ => s"Π(_: $ty1). $ty2(_)"
  )

  /**
   * Notation `A ->: B <=> Π(x :: A). B`
   * where B is independent on x
   */
  extension (a: Expr[Ind]) {
    infix def ->:(b: Expr[Ind]): Expr[Ind] =
      Pi(a)(λ(x, b))
  }
  object `->:`:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case SPi(a, lambda(x, b)) if !b.freeVars.contains(x) =>
          Some((a, b))
        case _ => None

  // Pattern extractor for the 'Pi' Shallow Embedding constant.
  // It allows matching expressions of the form Pi(T1)(T2) using the pattern SPi(T1, T2).
  object SPi:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind >>: Ind])] =
      e match
        // We match against the specific Constant 'Pi' being applied twice: App(App(Pi, T1), T2)
        case App(App(`Pi`, t1), t2) =>
          Some((t1.asInstanceOf[Expr[Ind]], t2.asInstanceOf[Expr[Ind >>: Ind]]))
        case _ => None

  object SArrow:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case SPi(t1, lambda(x, t2)) if !t2.freeVars.contains(x) =>
          Some((t1, t2))
        case _ => None

}
