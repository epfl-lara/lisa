package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import Definitions.*

/** This file proves basic properties about definitions given in [[Definitions]].
  */
object Properties extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val ℛ = variable[Ind]
  private val X, Y = variable[Ind]
  private val A, B = variable[Ind]

  extension (x: set) {
    private infix def ℛ(y: set): Expr[Prop] = (x, y) ∈ Properties.ℛ
  }

  //////////////////////////////////////////////////////////////////////////
  section("Basic theorems")

  /** Theorem --- If `ℛ` is a relation on `X` then `ℛ` is a relation.
    *
    *   `relationOn(ℛ, X) |- relation(ℛ)`
    */
  val relationOnIsRelation = Theorem(
    relationOn(ℛ)(X) |- relation(ℛ)
  ) {
    assume(relationOn(ℛ)(X))
    thenHave(ℛ ⊆ (X × X)) by Substitute(relationOn.definition)
    thenHave(∃(Y, ℛ ⊆ (X × Y))) by RightExists
    thenHave(∃(X, ∃(Y, ℛ ⊆ (X × Y)))) by RightExists
    thenHave(thesis) by Substitute(relation.definition)
  }

  /** Theorem --- If `ℛ` is a relation between `X` and `Y` then `dom(ℛ) ⊆ X`.
    */
  val relationDomainSubset = Theorem(
    relationBetween(ℛ)(X)(Y) |- dom(ℛ) ⊆ X
  ) {
    sorry
  }

  /** Theorem --- If `ℛ` is a relation between `X` and `Y` then `range(ℛ) ⊆ Y`.
    */
  val relationRangeSubset = Theorem(
    relationBetween(ℛ)(X)(Y) |- range(ℛ) ⊆ Y
  ) {
    sorry
  }

  /**
    * Theorem --- If `x ℛ y` then `x ∈ dom(ℛ)`.
    */
  val domainMembership = Theorem(
    (x ℛ y) |- x ∈ dom(ℛ)
  ) {
    sorry
  }

  /**
    * Theorem --- If `x ℛ y` then `y ∈ dom(ℛ)`.
    */
  val rangeMembership = Theorem(
    (x ℛ y) |- y ∈ range(ℛ)
  ) {
    sorry
  }

  /** Theorem --- If `ℛ` is a relation, then `ℛ ⊆ dom(ℛ) × range(ℛ)`.
    *
    *   `relation(ℛ) |- ℛ ⊆ dom(ℛ) × range(ℛ)`
    */
  val relationDomainRange = Theorem(
    relation(ℛ) |- ℛ ⊆ (dom(ℛ) × range(ℛ))
  ) {
    sorry
  }

  /** Theorem --- If `ℛ` is a relation on `X` and `x ∉ X` or `y ∉ X`
    * then `¬(x ℛ y)`.
    */
  val relationOutsideDomain = Theorem(
    (relationOn(ℛ)(X), (x ∉ X) \/ (y ∉ X)) |- ¬(x ℛ y)
  ) {
    assume(relationOn(ℛ)(X))
    thenHave(ℛ ⊆ (X × X)) by Substitute(relationOn.definition)
    thenHave((x, y) ∈ ℛ ==> (x ∈ X) /\ (y ∈ X)) by Tautology.fromLastStep(
      Subset.membership of (x := ℛ, y := (X × X), z := (x, y)),
      CartesianProduct.pairMembership of (A := X, B := X)
    )
    thenHave(thesis) by Tautology
  }


  //////////////////////////////////////////////////////////////////////////
  section("Reformulations")

  /** Theorem --- If `ℛ` is transitive, then `x ℛ y` and `y ℛ z` implies `x ℛ z`.
    *
    * Reformulation of the definition.
    */
  val appliedTransitivity = Theorem(
    (transitive(ℛ), x ℛ y, y ℛ z) |- (x ℛ z)
  ) {
    assume(transitive(ℛ))
    have(∀(x, ∀(y, ∀(z, (x ℛ y) /\ (y ℛ z) ==> (x ℛ z))))) by Tautology.from(transitive.definition)
    thenHave((x ℛ y) /\ (y ℛ z) ==> (x ℛ z)) by InstantiateForall(x, y, z)
    thenHave(thesis) by Restate
  }

  /** Theorem --- If `ℛ` is a relation on `X`, it suffices to show transitivity on `X`
    * to get full transitivity.
    */
  val restrictedTransitivity = Theorem(
    (relationOn(ℛ)(X), ∀(x, ∀(y, ∀(z, (x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x ℛ y) /\ (y ℛ z) ==> (x ℛ z))))) |- transitive(ℛ)
  ) {
    assume(relationOn(ℛ)(X))
    assume(∀(x, ∀(y, ∀(z, (x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x ℛ y) /\ (y ℛ z) ==> (x ℛ z)))))
    val assumption = thenHave((x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ (x ℛ y) /\ (y ℛ z) ==> (x ℛ z)) by InstantiateForall(x, y, z)

    // Since `ℛ` is a relation on `X`, it cannot be the case that `x ℛ y` if `x ∉ X` or `y ∉ X`.
    have((x ∉ X) \/ (y ∉ X) \/ (z ∉ X) |- ¬(x ℛ y) \/ ¬(y ℛ z)) by Tautology.from(
      relationOutsideDomain of (x := x, y := y),
      relationOutsideDomain of (x := y, y := z),
    )
    thenHave((x ℛ y) /\ (y ℛ z) ==> (x ℛ z)) by Tautology.fromLastStep(assumption)
    thenHave(∀(x, ∀(y, ∀(z, (x ℛ y) /\ (y ℛ z) ==> (x ℛ z))))) by Generalize
    thenHave(relation(ℛ) /\ ∀(x, ∀(y, ∀(z, (x ℛ y) /\ (y ℛ z) ==> (x ℛ z))))) by Tautology.fromLastStep(relationOnIsRelation)
    thenHave(thesis) by Substitute(transitive.definition)
  }

  /** Theorem --- If `ℛ` is total on `X`, then for `x, y ∈ X`, either `x ℛ y`,
    * `y ℛ x` or `x = y`.
    *
    * Reformulation of the definition.
    */
  val appliedTotality = Theorem(
    (total(ℛ)(X), x ∈ X, y ∈ X) |- (x ℛ y) \/ (y ℛ x) \/ (x === y)
  ) {
    assume(total(ℛ)(X))

    have(∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x ℛ y) \/ (y ℛ x) \/ (x === y)))) by Tautology.from(total.definition)
    thenHave((x ∈ X) /\ (y ∈ X) ==> (x ℛ y) \/ (y ℛ x) \/ (x === y)) by InstantiateForall(x, y)
    thenHave(thesis) by Restate
  }


  //////////////////////////////////////////////////////////////////////////
  section("Properties")


  /** Theorem --- Any irreflexive relation is not reflexive on a non-empty set.
    */
  val irreflexiveNotReflexive = Theorem(
    (irreflexive(ℛ), X ≠ ∅) |- ¬(reflexive(ℛ)(X))
  ) {
    assume(irreflexive(ℛ))
    assume(X ≠ ∅)

    have(∀(x, ¬(x ℛ x))) by Tautology.from(irreflexive.definition)
    thenHave(¬(x ℛ x)) by InstantiateForall(x)
    thenHave(x ∈ X |- x ∈ X /\ ¬(x ℛ x)) by Tautology
    thenHave(x ∈ X |- ∃(x, x ∈ X /\ ¬(x ℛ x))) by RightExists
    thenHave(∃(x, x ∈ X) |- ∃(x, x ∈ X /\ ¬(x ℛ x))) by LeftExists

    have(∃(x, x ∈ X /\ ¬(x ℛ x))) by Cut(EmptySet.nonEmptyHasElement of (x := X), lastStep)
    thenHave(thesis) by Tautology.fromLastStep(reflexive.definition)
  }


  /** Theorem --- Any asymmetric relation is irreflexive.
    */
  val asymmetricIrreflexive = Theorem(
    asymmetric(ℛ) |- irreflexive(ℛ)
  ) {
    assume(asymmetric(ℛ))
    have(∀(x, ∀(y, (x ℛ y) ==> ¬(y ℛ x)))) by Tautology.from(asymmetric.definition)
    thenHave((x ℛ x) ==> ¬(x ℛ x)) by InstantiateForall(x, x)
    thenHave(¬(x ℛ x)) by Tautology
    thenHave(∀(x, ¬(x ℛ x))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(asymmetric.definition, irreflexive.definition)
  }


  /** Theorem --- If `ℛ` is a total relation on `X` then `ℛ` is total on `Y ⊆ X`.
    */
  val totalSubset = Theorem(
    (total(ℛ)(X), Y ⊆ X) |- total(ℛ)(Y)
  ) {
    sorry
  }

}
