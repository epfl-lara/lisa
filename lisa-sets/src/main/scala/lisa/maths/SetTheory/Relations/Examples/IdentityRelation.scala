package lisa.maths.SetTheory.Relations
package Examples

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Predef._

/**
 * The identity or diagonal relation `Δ(X)` on `X` is the set of pairs `(x, x)`
 * for `x ∈ X`. It is the smallest [[equivalence]] relation on `X`.
 */
object IdentityRelation extends lisa.Main {

  private val X = variable[Ind]
  private val x, y = variable[Ind]
  private val R = variable[Ind]

  /**
   * Identity relation --- The identity relation on `X`, also called the
   * diagonal of `X`, is the set `Δ(X)` of pairs `(x, x)` for `x ∈ X`.
   */
  val Δ = DEF(λ(X, { (x, x) | x ∈ X }))

  /**
   * Theorem --- A relation `R` is reflexive on `X` <=> `Δ(X) ⊆ R`.
   */
  val subset = Theorem(
    Δ(X) ⊆ R <=> reflexive(R)(X)
  ) {
    have(z ∈ { (x, x) | x ∈ X } <=> ∃(x ∈ X, (x, x) === z)) by Replacement.apply
    val deltaMem = thenHave(z ∈ Δ(X) <=> ∃(x ∈ X, (x, x) === z)) by Substitute(Δ.definition)

    // Forward: Δ(X) ⊆ R ==> reflexive(R)(X)
    val forward = have(Δ(X) ⊆ R |- reflexive(R)(X)) subproof {
      assume(Δ(X) ⊆ R)
      have(x ∈ X |- (x, x) ∈ { (x, x) | x ∈ X }) by Tautology.from(Replacement.map of (A := X, F := λ(x, (x, x))))
      thenHave(x ∈ X |- (x, x) ∈ Δ(X)) by Substitute(Δ.definition)
      thenHave(x ∈ X |- (x, x) ∈ R) by Tautology.fromLastStep(Subset.membership of (x := Δ(X), y := R, z := (x, x)))
      thenHave(x ∈ X ==> (x, x) ∈ R) by Restate
      thenHave(∀(x, x ∈ X ==> (x, x) ∈ R)) by RightForall
      thenHave(∀(x ∈ X, (x, x) ∈ R)) by Restate
      thenHave(thesis) by Substitute(reflexive.definition)
    }

    // Backward: reflexive(R)(X) ==> Δ(X) ⊆ R
    val backward = have(reflexive(R)(X) |- Δ(X) ⊆ R) subproof {
      assume(reflexive(R)(X))
      have(∀(x ∈ X, (x, x) ∈ R)) by Tautology.from(reflexive.definition)
      thenHave(x ∈ X ==> (x, x) ∈ R) by InstantiateForall(x)
      thenHave(x ∈ X |- (x, x) ∈ R) by Restate
      thenHave((x ∈ X, (x, x) === z) |- z ∈ R) by Congruence
      thenHave(x ∈ X /\ ((x, x) === z) |- z ∈ R) by Restate
      thenHave(∃(x, x ∈ X /\ ((x, x) === z)) |- z ∈ R) by LeftExists
      thenHave(z ∈ Δ(X) ==> z ∈ R) by Tautology.fromLastStep(deltaMem)
      thenHave(∀(z, z ∈ Δ(X) ==> z ∈ R)) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := Δ(X), y := R))
    }

    have(thesis) by Tautology.from(forward, backward)
  }
}
