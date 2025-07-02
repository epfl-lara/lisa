package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef.*

import Definitions.*

/** The restriction of a function `f` to a domain `X` is the function `f↾X`, where `↾`
  * is the usual restriction on relations.
  *
  * TODO: Finish the proofs.
  */
object Restriction extends lisa.Main {

  private val f, g = variable[Ind]
  private val X = variable[Ind]
  private val x, y = variable[Ind]

  extension (f: set) {
    inline def apply(x: set): set = app(f)(x)
  }

  /** Definition --- The restriction of a function `f` to a domain `X` is the
    * function `f↾X`, where `↾` is the usual restriction on relations.
    */
  export Relations.Predef.↾

  /** Theorem --- If `f` is a function and `g ⊆ f` then `g` is a function.
    */
  val subsetIsFunction = Theorem(
    (function(f), g ⊆ f) |- function(g)
  ) {
    sorry
  }

  /** Theorem --- If `f` is a function then `f↾X` is also a function.
    */
  val restrictionIsFunction = Theorem(
    function(f) |- function(f ↾ X)
  ) {
    sorry
  }

  /** Theorem --- The restricted function `f↾X` agrees with `f` on `X`.
    */
  val restrictedApp = Theorem(
    (function(f), x ∈ X) |- (f ↾ X)(x) === f(x)
  ) {
    sorry
  }

  /** Theorem --- If `f` and `g` agree on `X`, then `f↾X = g↾X`.
    */
  val extensionality = Theorem(
    ∀(x, x ∈ X ==> (f(x) === g(x))) |- (f ↾ X) === (g ↾ X)
  ) {
    sorry
  }
}
