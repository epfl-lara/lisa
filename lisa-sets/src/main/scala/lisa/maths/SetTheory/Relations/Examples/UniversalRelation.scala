package lisa.maths.SetTheory.Relations
package Examples

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Predef._

/**
 * The universal relation on `X` is the relation `R` that relates every element
 * to every other element, i.e. `R = X × X`.
 */
object UniversalRelation extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val R, ~ = variable[Ind]
  private val A, B, X = variable[Ind]

  /**
   * Theorem --- The [[CartesianProduct]] `X × X` is the universal relation on `X`.
   */
  val isRelation = Theorem(
    relationOn(X × X)(X)
  ) {
    have(thesis) by Tautology.from(
      relationOn.definition of (R := X × X),
      Subset.reflexivity of (x := X × X)
    )
  }

  /**
   * Theorem --- The domain of the universal relation `X × X` is `X`.
   */
  val universalRelationDomain = Theorem(
    dom(X × X) === X
  ) {
    sorry
  }

  /**
   * Theorem --- The range of the universal relation `X × X` is `X`.
   */
  val universalRelationRange = Theorem(
    range(X × X) === X
  ) {
    sorry
  }

  /**
   * Theorem --- The universal relation `A × A` is reflexive on `A`.
   */
  val universalRelationReflexive = Theorem(
    reflexive(X × X)(X)
  ) {
    have(x ∈ X ==> (x, x) ∈ (X × X)) by Tautology.from(
      CartesianProduct.pairMembership of (x := x, y := x, A := X, B := X)
    )
    thenHave(∀(x ∈ X, (x, x) ∈ (X × X))) by RightForall
    thenHave(thesis) by Substitute(reflexive.definition of (R := X × X))
  }

  /**
   * Theorem --- The universal relation `A × A` is symmetric.
   */
  val universalRelationSymmetric = Theorem(
    symmetric(X × X)(X)
  ) {
    have((x ∈ X) /\ (y ∈ X) ==> ((x, y) ∈ (X × X) <=> (y, x) ∈ (X × X))) by Tautology.from(
      CartesianProduct.pairMembership of (x := x, y := y, A := X, B := X),
      CartesianProduct.pairMembership of (x := y, y := x, A := X, B := X)
    )
    thenHave(∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> ((x, y) ∈ (X × X) <=> (y, x) ∈ (X × X))))) by Generalize
    thenHave(∀(x ∈ X, ∀(y ∈ X, (x, y) ∈ (X × X) <=> (y, x) ∈ (X × X)))) by Tableau
    thenHave(thesis) by Substitute(symmetric.definition of (R := X × X))
  }

  /**
   * Theorem --- The universal relation `A × A` is transitive.
   */
  val universalRelationTransitive = Theorem(
    transitive(X × X)(X)
  ) {
    have((x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x, y) ∈ (X × X) /\ (y, z) ∈ (X × X) ==> (x, z) ∈ (X × X)) by Tautology.from(
      CartesianProduct.pairMembership of (x := x, y := y, A := X, B := X),
      CartesianProduct.pairMembership of (x := y, y := z, A := X, B := X),
      CartesianProduct.pairMembership of (x := x, y := z, A := X, B := X)
    )
    thenHave(∀(x, ∀(y, ∀(z, (x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x, y) ∈ (X × X) /\ (y, z) ∈ (X × X) ==> (x, z) ∈ (X × X))))) by Generalize
    thenHave(∀(x ∈ X, ∀(y ∈ X, ∀(z ∈ X, (x, y) ∈ (X × X) /\ (y, z) ∈ (X × X) ==> (x, z) ∈ (X × X))))) by Tableau
    thenHave(thesis) by Substitute(transitive.definition of (R := X × X))
  }

  /**
   * Theorem --- The universal relation `A × A` is an equivalence relation.
   */
  val universalRelationEquivalence = Theorem(
    equivalence(X × X)(X)
  ) {
    have(thesis) by Tautology.from(
      equivalence.definition of (`~` := X × X, A := X),
      isRelation,
      universalRelationReflexive,
      universalRelationSymmetric,
      universalRelationTransitive
    )
  }

  /**
   * Theorem --- The universal relation `A × A` is total.
   */
  val universalRelationTotal = Theorem(
    total(X × X)(X)
  ) {
    have((x ∈ X) /\ (y ∈ X) ==> (x, y) ∈ (X × X) \/ ((y, x) ∈ (X × X)) \/ (x === y)) by Tautology.from(
      CartesianProduct.pairMembership of (A := X, B := X)
    )
    thenHave(∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x, y) ∈ (X × X) \/ ((y, x) ∈ (X × X)) \/ (x === y)))) by Generalize
    thenHave(∀(x ∈ X, ∀(y ∈ X, (x, y) ∈ (X × X) \/ ((y, x) ∈ (X × X)) \/ (x === y)))) by Tableau
    thenHave(thesis) by Substitute(total.definition of (R := X × X))
  }

  /**
   * Theorem --- The universal relation `A × A` is strongly connected.
   */
  val universalRelationStronglyConnected = Theorem(
    stronglyConnected(X × X)(X)
  ) {
    have((x ∈ X) /\ (y ∈ X) ==> (x, y) ∈ (X × X) \/ ((y, x) ∈ (X × X))) by Tautology.from(
      CartesianProduct.pairMembership of (A := X, B := X)
    )
    thenHave(∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x, y) ∈ (X × X) \/ ((y, x) ∈ (X × X))))) by Generalize
    thenHave(∀(x ∈ X, ∀(y ∈ X, (x, y) ∈ (X × X) \/ ((y, x) ∈ (X × X))))) by Tableau
    thenHave(thesis) by Substitute(stronglyConnected.definition of (R := X × X))
  }
}
