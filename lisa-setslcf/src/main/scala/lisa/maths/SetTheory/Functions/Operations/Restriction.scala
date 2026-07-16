package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Predef._

import Function._

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

    /**
     * Notation `f ↾ A`.
     */
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
    val eq1 = have(x ∈ dom(f ↾ A) <=> ∃(z ∈ f, fst(z) ∈ A /\ (fst(z) === x))) by Tableau.from(
      lastStep,
      `x ∈ dom(f)` of (f := f ↾ A)
    )

    // Forward: ∃(z ∈ f, fst(z) ∈ A ∧ fst(z) = x) |- x ∈ dom(f) ∩ A
    have(fst(z) ∈ A |- fst(z) ∈ A) by Hypothesis
    val xInA = thenHave((fst(z) ∈ A, fst(z) === x) |- x ∈ A) by Congruence

    have((z ∈ f, fst(z) === x) |- z ∈ f /\ (fst(z) === x)) by Restate
    thenHave((z ∈ f, fst(z) === x) |- ∃(z, z ∈ f /\ (fst(z) === x))) by RightExists
    val xInDomF = thenHave((z ∈ f, fst(z) === x) |- x ∈ dom(f)) by Tautology.fromLastStep(`x ∈ dom(f)`)

    have(z ∈ f /\ (fst(z) ∈ A) /\ (fst(z) === x) |- x ∈ dom(f) /\ (x ∈ A)) by Tautology.from(xInA, xInDomF)
    thenHave(∃(z, z ∈ f /\ (fst(z) ∈ A) /\ (fst(z) === x)) |- x ∈ dom(f) /\ (x ∈ A)) by LeftExists
    val fwd = thenHave(x ∈ dom(f ↾ A) ==> x ∈ (dom(f) ∩ A)) by Tautology.fromLastStep(
      eq1,
      Intersection.membership of (z := x, x := dom(f), y := A)
    )

    // Backward: x ∈ dom(f) ∩ A |- ∃(z ∈ f, fst(z) ∈ A ∧ fst(z) = x)
    have(x ∈ A |- x ∈ A) by Hypothesis
    val fstInA = thenHave((x ∈ A, fst(z) === x) |- fst(z) ∈ A) by Congruence

    have((z ∈ f, fst(z) === x, fst(z) ∈ A) |- z ∈ f /\ (fst(z) ∈ A) /\ (fst(z) === x)) by Restate
    thenHave((z ∈ f, fst(z) === x, x ∈ A) |- z ∈ f /\ (fst(z) ∈ A) /\ (fst(z) === x)) by Tautology.fromLastStep(fstInA)
    thenHave((z ∈ f, fst(z) === x, x ∈ A) |- ∃(z, z ∈ f /\ (fst(z) ∈ A) /\ (fst(z) === x))) by RightExists
    thenHave((z ∈ f /\ (fst(z) === x), x ∈ A) |- ∃(z, z ∈ f /\ (fst(z) ∈ A) /\ (fst(z) === x))) by Restate
    thenHave((∃(z, z ∈ f /\ (fst(z) === x)), x ∈ A) |- ∃(z, z ∈ f /\ (fst(z) ∈ A) /\ (fst(z) === x))) by LeftExists
    val bwd = thenHave(x ∈ (dom(f) ∩ A) ==> x ∈ dom(f ↾ A)) by Tautology.fromLastStep(
      eq1,
      `x ∈ dom(f)`,
      Intersection.membership of (z := x, x := dom(f), y := A)
    )

    have(x ∈ dom(f ↾ A) <=> x ∈ (dom(f) ∩ A)) by Tautology.from(fwd, bwd)
    thenHave(thesis) by Extensionality
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
      EmptySet.definition of (x := z)
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
    assume(function(f))
    assume(g ⊆ f)

    val gIsFunc = have(function(g)) by Restate.from(BasicTheorems.subset)

    // Forward: z ∈ g → z ∈ f↾dom(g)
    val fwd = have(z ∈ g |- z ∈ (f ↾ dom(g))) subproof {
      assume(z ∈ g)
      val zInF = have(z ∈ f) by Tautology.from(Subset.membership of (x := g, y := f, z := z))
      have(fst(z) ∈ { fst(z) | z ∈ g }) by Tautology.from(Replacement.map of (x := z, A := g, F := fst))
      val fstInDomG = thenHave(fst(z) ∈ dom(g)) by Substitute(dom.definition of (R := g))
      have(thesis) by Tautology.from(membership of (A := dom(g)), zInF, fstInDomG)
    }

    // Backward: z ∈ f↾dom(g) → z ∈ g
    val bwd = have(z ∈ (f ↾ dom(g)) |- z ∈ g) subproof {
      assume(z ∈ (f ↾ dom(g)))
      val zInF = have(z ∈ f) by Tautology.from(membership of (A := dom(g)))
      val fstInDomG = have(fst(z) ∈ dom(g)) by Tautology.from(membership of (A := dom(g)))

      // z = (fst(z), snd(z)) since f is a function
      val zIsPair = have(z === (fst(z), snd(z))) by Tautology.from(BasicTheorems.inversion, zInF)
      val pairInF = have((fst(z), snd(z)) ∈ f) by Congruence.from(zInF, zIsPair)
      val fstInDomF = have(fst(z) ∈ dom(f)) by Tautology.from(BasicTheorems.domainMembership of (x := fst(z), y := snd(z)), pairInF)

      // f(fst(z)) = snd(z)
      val fApp = have(f(fst(z)) === snd(z)) by Tautology.from(
        BasicTheorems.appDefinition of (x := fst(z), y := snd(z)),
        fstInDomF,
        pairInF
      )

      // g(fst(z)) is defined and (fst(z), g(fst(z))) ∈ g
      val gAppInG = have((fst(z), g(fst(z))) ∈ g) by Tautology.from(
        BasicTheorems.appDefinition of (f := g, x := fst(z), y := g(fst(z))),
        gIsFunc,
        fstInDomG
      )

      // (fst(z), g(fst(z))) ∈ f since g ⊆ f
      val gAppInF = have((fst(z), g(fst(z))) ∈ f) by Tautology.from(
        Subset.membership of (x := g, y := f, z := (fst(z), g(fst(z)))),
        gAppInG
      )

      // f(fst(z)) = g(fst(z))
      val fEqG = have(f(fst(z)) === g(fst(z))) by Tautology.from(
        BasicTheorems.appDefinition of (x := fst(z), y := g(fst(z))),
        fstInDomF,
        gAppInF
      )

      // snd(z) = g(fst(z)), so (fst(z), snd(z)) ∈ g
      val sndEq = have(snd(z) === g(fst(z))) by Congruence.from(fApp, fEqG)
      have((fst(z), snd(z)) ∈ g) by Congruence.from(gAppInG, sndEq)
      thenHave(thesis) by Substitute(zIsPair)
    }

    have(z ∈ g <=> z ∈ (f ↾ dom(g))) by Tautology.from(fwd, bwd)
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- If `f` and `g` agree on `A`, and `A ⊆ dom(f)` and `A ⊆ dom(g)`, then `f↾A = g↾A`.
   */
  val extensionality = Theorem(
    (function(f), function(g), A ⊆ dom(f), A ⊆ dom(g), ∀(x ∈ A, f(x) === g(x))) |- (f ↾ A) === (g ↾ A)
  ) {
    assume(function(f))
    assume(function(g))
    assume(A ⊆ dom(f))
    assume(A ⊆ dom(g))
    assume(∀(x ∈ A, f(x) === g(x)))

    // Forward: z ∈ (f ↾ A) → z ∈ (g ↾ A)
    val fwd = have(z ∈ (f ↾ A) |- z ∈ (g ↾ A)) subproof {
      assume(z ∈ (f ↾ A))

      val zInF = have(z ∈ f) by Tautology.from(membership)
      val fstInA = have(fst(z) ∈ A) by Tautology.from(membership)

      // z = (fst(z), snd(z)) since function(f) and z ∈ f
      val zIsPair = have(z === (fst(z), snd(z))) by Tautology.from(BasicTheorems.inversion, zInF)
      val pairInF = have((fst(z), snd(z)) ∈ f) by Congruence.from(zInF, zIsPair)

      // fst(z) ∈ dom(f)
      val fstInDomF = have(fst(z) ∈ dom(f)) by Tautology.from(
        BasicTheorems.domainMembership of (x := fst(z), y := snd(z)),
        pairInF
      )

      // f(fst(z)) = snd(z)
      val fApp = have(f(fst(z)) === snd(z)) by Tautology.from(
        BasicTheorems.appDefinition of (x := fst(z), y := snd(z)),
        fstInDomF,
        pairInF
      )

      // fst(z) ∈ dom(g) from A ⊆ dom(g)
      val fstInDomG = have(fst(z) ∈ dom(g)) by Tautology.from(
        Subset.membership of (x := A, y := dom(g), z := fst(z)),
        fstInA
      )

      // f(fst(z)) = g(fst(z))
      have(∀(x ∈ A, f(x) === g(x))) by Hypothesis
      thenHave(fst(z) ∈ A ==> (f(fst(z)) === g(fst(z)))) by InstantiateForall(fst(z))
      val fEqG = thenHave(f(fst(z)) === g(fst(z))) by Tautology.fromLastStep(fstInA)

      // snd(z) = g(fst(z))
      val sndEq = have(snd(z) === g(fst(z))) by Congruence.from(fApp, fEqG)

      // (fst(z), g(fst(z))) ∈ g
      val gAppInG = have((fst(z), g(fst(z))) ∈ g) by Tautology.from(
        BasicTheorems.appDefinition of (f := g, x := fst(z), y := g(fst(z))),
        fstInDomG
      )

      // (fst(z), snd(z)) ∈ g
      have((fst(z), snd(z)) ∈ g) by Congruence.from(gAppInG, sndEq)
      // z ∈ g
      thenHave(z ∈ g) by Substitute(zIsPair)

      have(thesis) by Tautology.from(lastStep, fstInA, membership of (f := g))
    }

    // Backward: z ∈ (g ↾ A) → z ∈ (f ↾ A) (symmetric)
    val bwd = have(z ∈ (g ↾ A) |- z ∈ (f ↾ A)) subproof {
      assume(z ∈ (g ↾ A))

      val zInG = have(z ∈ g) by Tautology.from(membership of (f := g))
      val fstInA = have(fst(z) ∈ A) by Tautology.from(membership of (f := g))

      val zIsPair = have(z === (fst(z), snd(z))) by Tautology.from(BasicTheorems.inversion of (f := g), zInG)
      val pairInG = have((fst(z), snd(z)) ∈ g) by Congruence.from(zInG, zIsPair)

      val fstInDomG = have(fst(z) ∈ dom(g)) by Tautology.from(
        BasicTheorems.domainMembership of (f := g, x := fst(z), y := snd(z)),
        pairInG
      )

      // g(fst(z)) = snd(z)
      val gApp = have(g(fst(z)) === snd(z)) by Tautology.from(
        BasicTheorems.appDefinition of (f := g, x := fst(z), y := snd(z)),
        fstInDomG,
        pairInG
      )

      // fst(z) ∈ dom(f) from A ⊆ dom(f)
      val fstInDomF = have(fst(z) ∈ dom(f)) by Tautology.from(
        Subset.membership of (x := A, y := dom(f), z := fst(z)),
        fstInA
      )

      // f(fst(z)) = g(fst(z))
      have(∀(x ∈ A, f(x) === g(x))) by Hypothesis
      thenHave(fst(z) ∈ A ==> (f(fst(z)) === g(fst(z)))) by InstantiateForall(fst(z))
      val fEqG = thenHave(f(fst(z)) === g(fst(z))) by Tautology.fromLastStep(fstInA)

      // snd(z) = f(fst(z))
      val sndEq = have(snd(z) === f(fst(z))) by Congruence.from(gApp, fEqG)

      // (fst(z), f(fst(z))) ∈ f
      val fAppInF = have((fst(z), f(fst(z))) ∈ f) by Tautology.from(
        BasicTheorems.appDefinition of (x := fst(z), y := f(fst(z))),
        fstInDomF
      )

      // (fst(z), snd(z)) ∈ f
      have((fst(z), snd(z)) ∈ f) by Congruence.from(fAppInF, sndEq)
      // z ∈ f
      thenHave(z ∈ f) by Substitute(zIsPair)

      have(thesis) by Tautology.from(lastStep, fstInA, membership)
    }

    have(z ∈ (f ↾ A) <=> z ∈ (g ↾ A)) by Tautology.from(fwd, bwd)
    thenHave(thesis) by Extensionality
  }
}
