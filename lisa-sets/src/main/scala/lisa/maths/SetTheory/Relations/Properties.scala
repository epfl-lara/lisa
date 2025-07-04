package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import Definitions.*

/**
 * This file proves basic properties about definitions given in [[Definitions]].
 */
object Properties extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val R = variable[Ind]
  private val X, Y = variable[Ind]
  private val A, B = variable[Ind]

  extension (x: set) {
    private infix def R(y: set): Expr[Prop] = (x, y) ∈ Properties.R
  }

  //////////////////////////////////////////////////////////////////////////
  section("Basic theorems")

  /**
   * Theorem --- If `R` is a relation on `X` then `R` is a relation.
   *
   *   `relationOn(R, X) |- relation(R)`
   */
  val relationOnIsRelation = Theorem(
    relationOn(R)(X) |- relation(R)
  ) {
    assume(relationOn(R)(X))
    thenHave(R ⊆ (X × X)) by Substitute(relationOn.definition)
    thenHave(∃(Y, R ⊆ (X × Y))) by RightExists
    thenHave(∃(X, ∃(Y, R ⊆ (X × Y)))) by RightExists
    thenHave(thesis) by Substitute(relation.definition)
  }

  /**
   * Theorem --- If `R` only contains pairs, then it is a relation.
   */
  val setOfPairsIsRelation = Theorem(
    ∀(z, z ∈ R ==> ∃(x, ∃(y, z === (x, y)))) |- relation(R)
  ) {
    sorry
  }

  /**
   * Theorem --- If `R` is a relation between `X` and `Y` then `dom(R) ⊆ X`.
   */
  val relationDomainSubset = Theorem(
    relationBetween(R)(X)(Y) |- dom(R) ⊆ X
  ) {
    sorry
  }

  /**
   * Theorem --- If `R` is a relation between `X` and `Y` then `range(R) ⊆ Y`.
   */
  val relationRangeSubset = Theorem(
    relationBetween(R)(X)(Y) |- range(R) ⊆ Y
  ) {
    sorry
  }

  /**
   * Theorem --- If `x R y` then `x ∈ dom(R)`.
   */
  val domainMembership = Theorem(
    (x R y) |- x ∈ dom(R)
  ) {
    sorry
  }

  /**
   * Theorem --- If `x R y` then `y ∈ dom(R)`.
   */
  val rangeMembership = Theorem(
    (x R y) |- y ∈ range(R)
  ) {
    sorry
  }

  /**
   * Theorem --- If `R` is a relation, then `R ⊆ dom(R) × range(R)`.
   *
   *   `relation(R) |- R ⊆ dom(R) × range(R)`
   */
  val relationDomainRange = Theorem(
    relation(R) |- R ⊆ (dom(R) × range(R))
  ) {
    sorry
  }

  /**
   * Theorem --- If `R` is a relation on `X` and `x ∉ X` or `y ∉ X`
   * then `¬(x R y)`.
   */
  val relationOutsideDomain = Theorem(
    (relationOn(R)(X), (x ∉ X) \/ (y ∉ X)) |- ¬(x R y)
  ) {
    assume(relationOn(R)(X))
    thenHave(R ⊆ (X × X)) by Substitute(relationOn.definition)
    thenHave((x, y) ∈ R ==> (x ∈ X) /\ (y ∈ X)) by Tautology.fromLastStep(
      Subset.membership of (x := R, y := (X × X), z := (x, y)),
      CartesianProduct.pairMembership of (A := X, B := X)
    )
    thenHave(thesis) by Tautology
  }

  //////////////////////////////////////////////////////////////////////////
  section("Reformulations")

  /**
   * Theorem --- If `R` is transitive, then `x R y` and `y R z` implies `x R z`.
   *
   * Reformulation of the definition.
   */
  val appliedTransitivity = Theorem(
    (transitive(R), x R y, y R z) |- (x R z)
  ) {
    assume(transitive(R))
    have(∀(x, ∀(y, ∀(z, (x R y) /\ (y R z) ==> (x R z))))) by Tautology.from(transitive.definition)
    thenHave((x R y) /\ (y R z) ==> (x R z)) by InstantiateForall(x, y, z)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- If `R` is a relation on `X`, it suffices to show transitivity on `X`
   * to get full transitivity.
   */
  val restrictedTransitivity = Theorem(
    (relationOn(R)(X), ∀(x, ∀(y, ∀(z, (x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x R y) /\ (y R z) ==> (x R z))))) |- transitive(R)
  ) {
    assume(relationOn(R)(X))
    assume(∀(x, ∀(y, ∀(z, (x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x R y) /\ (y R z) ==> (x R z)))))
    val assumption = thenHave((x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x R y) /\ (y R z) ==> (x R z)) by InstantiateForall(x, y, z)

    // Since `R` is a relation on `X`, it cannot be the case that `x R y` if `x ∉ X` or `y ∉ X`.
    have((x ∉ X) \/ (y ∉ X) \/ (z ∉ X) |- ¬(x R y) \/ ¬(y R z)) by Tautology.from(
      relationOutsideDomain of (x := x, y := y),
      relationOutsideDomain of (x := y, y := z)
    )
    thenHave((x R y) /\ (y R z) ==> (x R z)) by Tautology.fromLastStep(assumption)
    thenHave(∀(x, ∀(y, ∀(z, (x R y) /\ (y R z) ==> (x R z))))) by Generalize
    thenHave(relation(R) /\ ∀(x, ∀(y, ∀(z, (x R y) /\ (y R z) ==> (x R z))))) by Tautology.fromLastStep(relationOnIsRelation)
    thenHave(thesis) by Substitute(transitive.definition)
  }

  /**
   * Theorem --- If `R` is total on `X`, then for `x, y ∈ X`, either `x R y`,
   * `y R x` or `x = y`.
   *
   * Reformulation of the definition.
   */
  val appliedTotality = Theorem(
    (total(R)(X), x ∈ X, y ∈ X) |- (x R y) \/ (y R x) \/ (x === y)
  ) {
    assume(total(R)(X))

    have(∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x R y) \/ (y R x) \/ (x === y)))) by Tautology.from(total.definition)
    thenHave((x ∈ X) /\ (y ∈ X) ==> (x R y) \/ (y R x) \/ (x === y)) by InstantiateForall(x, y)
    thenHave(thesis) by Restate
  }

  //////////////////////////////////////////////////////////////////////////
  section("Properties")

  /**
   * Theorem --- Any irreflexive relation is not reflexive on a non-empty set.
   */
  val irreflexiveNotReflexive = Theorem(
    (irreflexive(R), X ≠ ∅) |- ¬(reflexive(R)(X))
  ) {
    assume(irreflexive(R))
    assume(X ≠ ∅)

    have(∀(x, ¬(x R x))) by Tautology.from(irreflexive.definition)
    thenHave(¬(x R x)) by InstantiateForall(x)
    thenHave(x ∈ X |- x ∈ X /\ ¬(x R x)) by Tautology
    thenHave(x ∈ X |- ∃(x, x ∈ X /\ ¬(x R x))) by RightExists
    thenHave(∃(x, x ∈ X) |- ∃(x, x ∈ X /\ ¬(x R x))) by LeftExists

    have(∃(x, x ∈ X /\ ¬(x R x))) by Cut(EmptySet.nonEmptyHasElement of (x := X), lastStep)
    thenHave(thesis) by Tautology.fromLastStep(reflexive.definition)
  }

  /**
   * Theorem --- Any asymmetric relation is irreflexive.
   */
  val asymmetricIrreflexive = Theorem(
    asymmetric(R) |- irreflexive(R)
  ) {
    assume(asymmetric(R))
    have(∀(x, ∀(y, (x R y) ==> ¬(y R x)))) by Tautology.from(asymmetric.definition)
    thenHave((x R x) ==> ¬(x R x)) by InstantiateForall(x, x)
    thenHave(¬(x R x)) by Tautology
    thenHave(∀(x, ¬(x R x))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(asymmetric.definition, irreflexive.definition)
  }

}
