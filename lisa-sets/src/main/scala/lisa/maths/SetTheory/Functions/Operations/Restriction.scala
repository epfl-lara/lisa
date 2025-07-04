package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Operations.Restriction as RelationRestriction

import Definitions.*

/** The restriction of a function `f` to a domain `X` is the function `f↾X`, where `↾`
  * is the usual restriction on relations.
  *
  * The restriction of a function `f` to `X` is also a function that agrees with `f` on `X`:
  * for all `x ∈ X` we have `(f ↾ X)(x) === f(x)` (see [[Restriction.agreement]]).
  *
  * TODO: Finish the proofs.
  */
object Restriction extends lisa.Main {

  private val f, g = variable[Ind]
  private val X = variable[Ind]
  private val x, y = variable[Ind]
  private val ℛ = variable[Ind]

  extension (f: set) {
    inline def apply(x: set): set = app(f)(x)
  }

  /** Definition --- The restriction of a function `f` to a domain `X` is the
    * function `f↾X`, where `↾` is the usual restriction on relations.
    */
  export RelationRestriction.↾

  /**
    * Theorem --- `(f ↾ X)(x) = y` if and only if `x ∈ X` and `f(x) = y`.
    */
  val restrictedApp = Theorem(
    function(f) |- ((f ↾ X)(x) === y) <=> (f(x) === y) /\ (x ∈ X)
  ) {
    have((x, y) ∈ (f ↾ X) <=> (x, y) ∈ f /\ (x ∈ X)) by Restate.from(RelationRestriction.membership of (ℛ := f))
    sorry
  }

  /**
    * Theorem --- For all `x ∈ X` we have `(f ↾ X)(x) = f(x)`.
    *
    * Consequence of [[restrictedApp]].
    */
  val agreement = Theorem(
    (function(f), x ∈ X) |- (f ↾ X)(x) === f(x)
  ) {
    have(thesis) by Tautology.from(restrictedApp of (y := f(x)))
  }

  /**
    * Theorem --- Restricting a function to the empty domain yields the empty set.
    */
  val emptyRestriction = Theorem(
    (f ↾ ∅) === ∅
  ) {
    have(thesis) by Restate.from(RelationRestriction.emptyRestriction of (ℛ := f))
  }

  /**
    * Theorem --- Restricting a function to its domain yields the function back.
    */
  val restrictionToDomain = Theorem(
    (f ↾ dom(f)) === f
  ) {
    have(thesis) by Restate.from(RelationRestriction.restrictionToDomain of (ℛ := f))
  }

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

  /** Theorem --- If `f` and `g` agree on `X`, then `f↾X = g↾X`.
    */
  val extensionality = Theorem(
    ∀(x, x ∈ X ==> (f(x) === g(x))) |- (f ↾ X) === (g ↾ X)
  ) {
    sorry
  }
}
