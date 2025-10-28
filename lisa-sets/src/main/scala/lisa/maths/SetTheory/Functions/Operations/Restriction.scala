package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.*

import Function.*

/**
  * The restriction of a function `f` to a domain `A` is the function `f↾A` that
  * agrees with `f` such that `dom(f ↾ A) = dom(f) ∩ A`.
  *
  * TODO: Finish the proofs.
  */
object Restriction extends lisa.Main {

  extension (f: Expr[Ind]) {
    def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * Restriction --- For a function `f`, its restriction to `A` is the function
   * `f↾A` that agrees with `f` such that `dom(f ↾ A) = dom(f) ∩ A`. In other
   * words,
   *
   *   `f↾A = {(x, y) ∈ f | x ∈ A}`
   */
  val restriction = DEF(λ(f, λ(A, { z ∈ f | fst(z) ∈ A }))).printAs(args => {
    val f = args(0)
    val A = args(1)
    s"${f}↾${A}"
  })

  extension (f: Expr[Ind]) {
    /** Notation `f ↾ A`. */
    infix def ↾(A: Expr[Ind]): Expr[Ind] = restriction(f)(A)
  }

  /**
    * Theorem --- We have `z ∈ (f ↾ A)` if and only `z ∈ f` and `fst(z) ∈ A`.
    */
  val membership = Theorem(
    z ∈ (f ↾ A) <=> (z ∈ f) /\ (fst(z) ∈ A)
  ) {
    have(z ∈ { z ∈ f | fst(z) ∈ A } <=> z ∈ f /\ (fst(z) ∈ A)) by Comprehension.apply
    thenHave(thesis) by Substitute(restriction.definition)
  }

  /**
    * Theorem --- We have `(x, y) ∈ (f ↾ A)` if and only `(x, y) ∈ f` and `x ∈ A`.
    */
  val pairMembership = Theorem(
    (x, y) ∈ (f ↾ A) <=> ((x, y) ∈ f) /\ (x ∈ A)
  ) {
    have(thesis) by Congruence.from(membership of (z := (x, y)), Pair.pairFst)
  }

  /**
    * Theorem --- `f ↾ A ⊆ f`.
    */
  val isSubset = Theorem(
    (f ↾ A) ⊆ f
  ) {
    have(thesis) by Substitute(restriction.definition)(Comprehension.subset of (y := f, φ := λ(z, fst(z) ∈ A)))
  }

  /**
   * Theorem --- If `f` is a function then `f↾A` is also a function.
   */
  val isFunction = Theorem(
    function(f) |- function(f ↾ A)
  ) {
    have(thesis) by Cut(isSubset, BasicTheorems.subset of (g := (f ↾ A)))
  }

  /**
    * Theorem --- The domain of `f ↾ A` is `dom(f) ∩ A`.
    */
  val domain = Theorem(
    dom(f ↾ A) === (dom(f) ∩ A)
  ) {
    have(x ∈ { fst(z) | z ∈ f } <=> ∃(z ∈ f, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(f)` = thenHave(x ∈ dom(f) <=> ∃(z ∈ f, fst(z) === x)) by Substitute(dom.definition of (R := f))

    have(∀(z, z ∈ (f ↾ A) <=> (z ∈ f) /\ (fst(z) ∈ A))) by RightForall(membership)
    have(x ∈ dom(f ↾ A) <=> ∃(z ∈ f, fst(z) ∈ A /\ (fst(z) === x))) by Tableau.from(
      lastStep,
      `x ∈ dom(f)` of (f := f ↾ A)
    )

    sorry
  }

  /**
   * Theorem --- For all `x ∈ dom(f) ∩ A` we have `(f ↾ A)(x) = f(x)`.
   */
  val restrictedApp = Theorem(
    (function(f), x ∈ dom(f), x ∈ A) |- (f ↾ A)(x) === f(x)
  ) {
    assume(function(f))
    assume(x ∈ dom(f))
    assume(x ∈ A)

    have(x ∈ (dom(f) ∩ A)) by Tautology.from(Intersection.membership of (z := x, x := dom(f), y := A))
    thenHave(x ∈ dom(f ↾ A)) by Substitute(domain)
    thenHave(thesis) by Tautology.fromLastStep(
      BasicTheorems.appDefinition of (f := f ↾ A, y := f(x)),
      BasicTheorems.appDefinition of (f := f, y := f(x)),
      isFunction,
      pairMembership of (y := f(x))
    )
  }

  /**
   * Theorem --- Restricting a function to the empty domain yields the empty set.
   */
  val emptyRestriction = Theorem(
    (f ↾ ∅) === ∅
  ) {
    have(z ∈ (f ↾ ∅) <=> z ∈ f /\ (fst(z) ∈ ∅)) by Restate.from(membership of (A := ∅))
    thenHave(z ∈ (f ↾ ∅) <=> z ∈ ∅) by Tautology.fromLastStep(
      EmptySet.definition of (x := fst(z)),
      EmptySet.definition of (x := z),
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- Restricting a function to its domain yields the function back.
   */
  val restrictionToDomain = Theorem(
    (f ↾ dom(f)) === f
  ) {
    have(z ∈ f |- fst(z) ∈ { fst(z) | z ∈ f }) by Restate.from(Replacement.map of (x := z, A := f, F := fst))
    thenHave(z ∈ f |- fst(z) ∈ dom(f)) by Substitute(dom.definition of (R := f))
    thenHave(z ∈ (f ↾ dom(f)) <=> (z ∈ f)) by Tautology.fromLastStep(membership of (A := dom(f)))
    thenHave(thesis) by Extensionality
  }

  /**
    * Theorem --- We have that `(f ↾ A) ↾ B = f ↾ (A ∩ B)`.
    */
  val doubleRestriction = Theorem(
    (f ↾ A) ↾ B === (f ↾ (A ∩ B))
  ) {
    have(z ∈ ((f ↾ A) ↾ B) <=> (z ∈ (f ↾ (A ∩ B)))) by Tautology.from(
      membership,
      membership of (f := f ↾ A, A := B),
      membership of (A := (A ∩ B)),
      Intersection.membership of (z := fst(z), x := A, y := B)
    )
    thenHave(thesis) by Extensionality
  }

  /**
    * Theorem --- If `f` is a function and `g ⊆ f` then `g = f↾dom(g)`.
    */
  val subsetIsRestriction = Theorem(
    (function(f), g ⊆ f) |- (g === f ↾ dom(g))
  ) {
    sorry
  }

  /**
   * Theorem --- If `f` and `g` agree on `A`, then `f↾A = g↾A`.
   */
  val extensionality = Theorem(
    (function(f), function(g), ∀(x ∈ A, f(x) === g(x))) |- (f ↾ A) === (g ↾ A)
  ) {
    assume(function(f))
    assume(function(g))
    assume(∀(x ∈ A, f(x) === g(x)))

    sorry
  }
}
