package lisa.maths.SetTheory.Relations.Examples

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.*

/** The universal relation on `X` is the relation `ℛ` that relates every element
  * to every other element, i.e. `ℛ = X × X`.
  */
object UniversalRelation extends lisa.Main {

  private val x, y = variable[Ind]
  private val a, b = variable[Ind]
  private val ℛ = variable[Ind]
  private val A, B, X = variable[Ind]

  /** Theorem --- The [[CartesianProduct]] `X × X` is the universal relation on `X`.
    */
  val universalRelation = Theorem(
    relationOn(X × X)(X)
  ) {
    have(thesis) by Tautology.from(
      relationOn.definition of (ℛ := X × X),
      Subset.reflexivity of (x := X × X)
    )
  }

  /** Theorem --- The domain of the universal relation `X × X` is `X`.
    */
  val universalRelationDomain = Theorem(
    dom(X × X) === X
  ) {
    sorry
  }

  /** Theorem --- The range of the universal relation `X × X` is `X`.
    */
  val universalRelationRange = Theorem(
    range(X × X) === X
  ) {
    sorry
  }

  /** Theorem --- The universal relation `A × A` is reflexive on `A`.
    */
  val universalRelationReflexive = Theorem(
    reflexive(X × X)(X)
  ) {
    have(x ∈ X ==> (x, x) ∈ (X × X)) by Tautology.from(
      CartesianProduct.pairMembership of (x := x, y := x, A := X, B := X)
    )
    thenHave(∀(x, x ∈ X ==> (x, x) ∈ (X × X))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      reflexive.definition of (ℛ := X × X),
      universalRelation
    )
  }

  /** Theorem --- The universal relation `A × A` is symmetric.
    */
  val universalRelationSymmetric = Theorem(
    symmetric(X × X)
  ) {
    sorry
  }

  /** Theorem --- The universal relation `A × A` is transitive.
    */
  val universalRelationTransitive = Theorem(
    transitive(X × X)
  ) {
    sorry
  }

  /** Theorem --- The universal relation `A × A` is an equivalence relation.
    */
  val universalRelationEquivalence = Theorem(
    equivalence(X × X)(X)
  ) {
    have(thesis) by Tautology.from(
      equivalence.definition of (ℛ := X × X),
      universalRelationReflexive,
      universalRelationSymmetric,
      universalRelationTransitive
    )
  }

  /** Theorem --- The universal relation `A × A` is total.
    */
  val universalRelationTotal = Theorem(
    total(X × X)(X)
  ) {
    sorry
  }

  /** Theorem --- The universal relation `A × A` is strongly connected.
    */
  val universalRelationStronglyConnected = Theorem(
    stronglyConnected(X × X)(X)
  ) {
    sorry
  }
}
