package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.{*, given}

import Function.*
import Restriction.*

/**
 * If `f` and `g` are two functions that agree on the intersection of their
 * domains, then `f ∪ g` is a function on the union of their domains.
 *
 * Note that in general, the union of two functions is not a function, as they
 * may disagree on the intersection of their domains.
 */
object Union extends lisa.Main {

  private val 𝓕 = variable[Ind]

  extension (f: Expr[Ind]) {
    private def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * Theorem --- The union of a set of functions that agree on the intersection
   * of their domains is a function.
   */
  val isFunction = Theorem(
    (
      ∀(f ∈ 𝓕, function(f)),
      ∀(f ∈ 𝓕, ∀(g ∈ 𝓕, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))))
    ) |- function(⋃(𝓕))
  ) {
    assume(∀(f ∈ 𝓕, function(f)))
    assume(∀(f ∈ 𝓕, ∀(g ∈ 𝓕, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x)))))

    sorry
  }

  /**
    * Theorem --- The domain of the unions is the ∪ of the domains.
    */
  val domain = Theorem(
    dom(⋃(𝓕)) === ⋃({ dom(f) | f ∈ 𝓕})
  ) {
    have(x ∈ { fst(z) | z ∈ f } <=> ∃(z ∈ f, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(f)` = thenHave(x ∈ dom(f) <=> ∃(z ∈ f, fst(z) === x)) by Substitute(dom.definition of (R := f))

    have(z ∈ ⋃(𝓕) <=> ∃(f ∈ 𝓕, z ∈ f)) by Tautology.from(⋃.definition of (x := 𝓕))
    thenHave(∀(z, z ∈ ⋃(𝓕) <=> ∃(f ∈ 𝓕, z ∈ f))) by RightForall

    /*
    have(x ∈ dom(⋃(𝓕)) <=> ∃(f ∈ 𝓕, ∃(z ∈ f, fst(z) === x))) by Tableau.from(
      `x ∈ dom(f)` of (f := ⋃(𝓕)),
      lastStep,
    )
     */

    sorry
  }

}
