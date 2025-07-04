package lisa.maths.SetTheory.Functions

import lisa.maths.SetTheory.Base.Predef.{*, given}
import Definitions.*

/** This file contains proofs of basic properties about functions.
  *
  * TODO: Add constant functions
  * TODO: Add Cantor's theorem (probably in a distinct file, when we get to cardinals).
  */
object Properties extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val A, B = variable[Ind]
  private val f, g = variable[Ind]

  extension (f: set) {

    /** Syntax for `f(x)`.
      */
    def apply(x: set): set = app(f)(x)
  }

  /** Lemma --- If `f : A -> B` then `f` is a function.
    */
  val functionBetweenIsFunction = Lemma(
    f :: A -> B |- function(f)
  ) {
    assume(f :: A -> B)
    thenHave(∃(B, f :: A -> B)) by RightExists
    thenHave(∃(A, ∃(B, f :: A -> B))) by RightExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /** Theorem --- If `f : A -> B` then `dom(f) = A`.
    */
  val functionDomain = Theorem(
    f :: A -> B |- dom(f) === A
  ) {
    sorry
  }

  /** Theorem --- If `f : A -> B` then `range(f) ⊆ B`.
    */
  val functionRange = Theorem(
    f :: A -> B |- range(f) ⊆ B
  ) {
    sorry
  }

  /**
    * Theorem --- `(x, y) ∈ f` if and only if `f(x) = y`.
    */
  val appDefinition = Theorem(
    function(f) |- (x, y) ∈ f <=> (f(x) === y)
  ) {
    sorry
  }

  /** Theorem --- If `f` is a function and `x ∈ dom(f)` then `f(x) ∈ range(f)`.
    */
  val appInRange = Theorem(
    (function(f), x ∈ dom(f)) |- f(x) ∈ range(f)
  ) {
    sorry
  }

  /** Theorem --- If `f : A -> B` and `x ∈ A` then `f(x) ∈ B`.
    *
    * Special case of [[appInRange]].
    */
  val appTyping = Theorem(
    (f :: A -> B, x ∈ A) |- (f(x) ∈ B)
  ) {
    assume(f :: A -> B)
    assume(x ∈ A)
    have(x ∈ dom(f)) by Congruence.from(functionDomain)
    thenHave(f(x) ∈ range(f)) by Tautology.fromLastStep(
      functionBetweenIsFunction,
      appInRange
    )
    thenHave(thesis) by Tautology.fromLastStep(
      functionRange,
      Subset.membership of (x := range(f), y := B, z := f(x))
    )
  }

  /** Theorem --- If `f` and `g` are functions on `A` such that `f(x) = g(x)`
    * for all `x ∈ A`, then `f` equals `g`.
    */
  val extensionality = Theorem(
    (
      functionOn(f)(A),
      functionOn(g)(A),
      ∀(x, x ∈ A ==> (f(x) === g(x)))
    ) |- (f === g)
  ) {
    sorry
  }

}
