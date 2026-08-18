package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef.{_, given}

import Relation._
import Properties._

/**
 * This file proves basic theorems about definitions given in [[Relation]] and
 * [[Properties]].
 */
object BasicTheorems extends lisa.Main {

  private val S = variable[Ind]

  /////////////////////////////////////////////////////////////////////////////
  section("Membership")

  /**
   * Theorem --- If `R` is a relation and `z ∈ R` then `z` is a pair.
   */
  val inversion = Theorem(
    (relation(R), z ∈ R) |- z === (fst(z), snd(z))
  ) {
    have((R ⊆ (X × Y), z ∈ R) |- z === (fst(z), snd(z))) by Tautology.from(
      CartesianProduct.inversion of (A := X, B := Y),
      Subset.membership of (x := R, y := (X × Y))
    )
    thenHave((∃(Y, R ⊆ (X × Y)), z ∈ R) |- z === (fst(z), snd(z))) by LeftExists
    thenHave((∃(X, ∃(Y, R ⊆ (X × Y))), z ∈ R) |- z === (fst(z), snd(z))) by LeftExists
    thenHave(thesis) by Substitute(relation.definition)
  }

  /**
   * Theorem --- If `x R y` then `x ∈ dom(R)`.
   */
  val domainMembership = Theorem(
    (x R y) |- x ∈ dom(R)
  ) {
    have((x R y) |- fst(x, y) ∈ { fst(z) | z ∈ R }) by Congruence.from(
      Replacement.map of (x := (x, y), A := R, F := fst)
    )
    have(thesis) by Congruence.from(
      lastStep,
      dom.definition,
      Pair.pairFst
    )
  }

  /**
   * Theorem --- If `x R y` then `y ∈ dom(R)`.
   */
  val rangeMembership = Theorem(
    (x R y) |- y ∈ range(R)
  ) {
    have((x R y) |- snd(x, y) ∈ { snd(z) | z ∈ R }) by Tautology.from(
      Replacement.map of (x := (x, y), A := R, F := snd)
    )
    have(thesis) by Congruence.from(
      lastStep,
      range.definition,
      Pair.pairSnd
    )
  }

  /**
   * Theorem --- If `R` is a relation then `R ⊆ (dom(R) × range(R))`.
   */
  val relationBetweenDomainRange = Theorem(
    relation(R) |- relationBetween(R)(dom(R))(range(R))
  ) {
    assume(relation(R))

    val `z is a pair` = have(z ∈ R |- z === (fst(z), snd(z))) by Restate.from(inversion)
    thenHave(z ∈ R |- (fst(z), snd(z)) ∈ R) by Congruence
    thenHave(z ∈ R |- fst(z) ∈ dom(R) /\ (snd(z) ∈ range(R))) by Tautology.fromLastStep(
      domainMembership of (x := fst(z), y := snd(z)),
      rangeMembership of (x := fst(z), y := snd(z))
    )
    thenHave(z ∈ R |- (fst(z), snd(z)) ∈ (dom(R) × range(R))) by Tautology.fromLastStep(
      CartesianProduct.pairMembership of (x := fst(z), y := snd(z), A := dom(R), B := range(R))
    )
    thenHave(z ∈ R |- z ∈ (dom(R) × range(R))) by Substitute(`z is a pair`)
    thenHave(z ∈ R ==> (z ∈ (dom(R) × range(R)))) by Restate
    thenHave(∀(z, z ∈ R ==> (z ∈ (dom(R) × range(R))))) by RightForall
    thenHave(R ⊆ (dom(R) × range(R))) by Substitute(⊆.definition of (x := R, y := (dom(R) × range(R))))
    thenHave(thesis) by Substitute(relationBetween.definition of (X := dom(R), Y := range(R)))
  }

  /////////////////////////////////////////////////////////////////////////////
  section("Relations between X and Y")

  /**
   * Theorem --- If `R` is a relation between `X` and `Y` then `R` is a relation.
   */
  val relationBetweenIsRelation = Theorem(
    relationBetween(R)(X)(Y) |- relation(R)
  ) {
    assume(relationBetween(R)(X)(Y))
    thenHave(R ⊆ (X × Y)) by Substitute(relationBetween.definition)
    thenHave(∃(Y, R ⊆ (X × Y))) by RightExists
    thenHave(∃(X, ∃(Y, R ⊆ (X × Y)))) by RightExists
    thenHave(thesis) by Substitute(relation.definition)
  }

  /**
   * Theorem --- If `R` is a relation between `X` and `Y` and `S ⊆ R`, then
   * `S` is also a relation between `X` and `Y`.
   */
  val subsetIsRelationBetween = Theorem(
    (relationBetween(R)(X)(Y), S ⊆ R) |- relationBetween(S)(X)(Y)
  ) {
    assume(relationBetween(R)(X)(Y))
    thenHave(R ⊆ (X × Y)) by Substitute(relationBetween.definition)
    thenHave(S ⊆ R |- S ⊆ (X × Y)) by Tautology.fromLastStep(
      Subset.transitivity of (x := S, y := R, z := (X × Y))
    )
    thenHave(thesis) by Substitute(relationBetween.definition of (R := S))
  }

  /**
   * Theorem --- If `R` is a relation between `X` and `Y` then `dom(R) ⊆ X`.
   */
  val relationBetweenDomain = Theorem(
    relationBetween(R)(X)(Y) |- dom(R) ⊆ X
  ) {
    assume(relationBetween(R)(X)(Y))

    have(x ∈ { fst(z) | z ∈ R } <=> ∃(z ∈ R, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(R)` = thenHave(x ∈ dom(R) <=> ∃(z ∈ R, fst(z) === x)) by Substitute(dom.definition)

    // We show that for any `z ∈ R` we have `fst(z) ∈ X`
    have(z ∈ R |- fst(z) ∈ X) by Tautology.from(
      relationBetween.definition,
      Subset.membership of (x := R, y := (X × Y)),
      CartesianProduct.fstMembership of (A := X, B := Y)
    )
    thenHave((z ∈ R, fst(z) === x) |- x ∈ X) by Congruence
    thenHave((z ∈ R) /\ (fst(z) === x) |- x ∈ X) by Restate
    thenHave(∃(z ∈ R, fst(z) === x) |- x ∈ X) by LeftExists
    thenHave(x ∈ dom(R) ==> (x ∈ X)) by Tautology.fromLastStep(`x ∈ dom(R)`)
    thenHave(∀(x, x ∈ dom(R) ==> (x ∈ X))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := dom(R), y := X))
  }

  /**
   * Theorem --- If `R` is a relation between `X` and `Y` then `range(R) ⊆ Y`.
   */
  val relationBetweenRange = Theorem(
    relationBetween(R)(X)(Y) |- range(R) ⊆ Y
  ) {
    assume(relationBetween(R)(X)(Y))

    have(y ∈ { snd(z) | z ∈ R } <=> ∃(z ∈ R, snd(z) === y)) by Replacement.apply
    val `y ∈ range(R)` = thenHave(y ∈ range(R) <=> ∃(z ∈ R, snd(z) === y)) by Substitute(range.definition)

    // We show that for any `z ∈ R` we have `snd(z) ∈ Y`
    have(z ∈ R |- snd(z) ∈ Y) by Tautology.from(
      relationBetween.definition,
      Subset.membership of (x := R, y := (X × Y)),
      CartesianProduct.sndMembership of (A := X, B := Y)
    )
    thenHave((z ∈ R, snd(z) === y) |- y ∈ Y) by Congruence
    thenHave((z ∈ R) /\ (snd(z) === y) |- y ∈ Y) by Restate
    thenHave(∃(z ∈ R, snd(z) === y) |- y ∈ Y) by LeftExists
    thenHave(y ∈ range(R) ==> (y ∈ Y)) by Tautology.fromLastStep(`y ∈ range(R)`)
    thenHave(∀(y, y ∈ range(R) ==> (y ∈ Y))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := range(R), y := Y))
  }

  /////////////////////////////////////////////////////////////////////////////
  section("Relations on X")

  /**
   * Theorem --- `R` is a relation on `X` if and only if `R` is a relation between
   * `X` and itself.
   */
  val relationOnIsRelationBetween = Theorem(
    relationOn(R)(X) <=> relationBetween(R)(X)(X)
  ) {
    have(thesis) by Tautology.from(relationOn.definition, relationBetween.definition of (Y := X))
  }

  /**
   * Theorem --- If `R` is a relation on `X` then `R` is a relation.
   *
   *   `relationOn(R, X) |- relation(R)`
   */
  val relationOnIsRelation = Theorem(
    relationOn(R)(X) |- relation(R)
  ) {
    have(thesis) by Tautology.from(relationOnIsRelationBetween, relationBetweenIsRelation of (Y := X))
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
  section("Quantifier-free applications")
  // TODO: These theorems should be removed, as they are basic applications.

  /**
   * Theorem --- If `R` is transitive, then `x R y` and `y R z` implies `x R z`.
   *
   * Quantifier-free reformulation of the definition.
   */
  val appliedTransitivity = Theorem(
    (transitive(R)(X), x ∈ X, y ∈ X, z ∈ X, x R y, y R z) |- (x R z)
  ) {
    assume(transitive(R)(X))
    have(∀(x ∈ X, ∀(y ∈ X, ∀(z ∈ X, (x R y) /\ (y R z) ==> (x R z))))) by Tautology.from(transitive.definition)
    thenHave(∀(x, ∀(y, ∀(z, x ∈ X /\ (y ∈ X) /\ (z ∈ X) /\ (x R y) /\ (y R z) ==> (x R z))))) by Tableau
    thenHave(x ∈ X /\ (y ∈ X) /\ (z ∈ X) /\ (x R y) /\ (y R z) ==> (x R z)) by InstantiateForall(x, y, z)
    thenHave(thesis) by Restate
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

    have(∀(x ∈ X, ∀(y ∈ X, (x R y) \/ (y R x) \/ (x === y)))) by Tautology.from(total.definition)
    thenHave(∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> (x R y) \/ (y R x) \/ (x === y)))) by Tableau
    thenHave((x ∈ X) /\ (y ∈ X) ==> (x R y) \/ (y R x) \/ (x === y)) by InstantiateForall(x, y)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- If `R` is irreflexive on `X`, then for `x ∈ X` we have `¬(x R x)`.
   *
   * Reformulation of the definition.
   */
  val appliedIrreflexivity = Theorem(
    (irreflexive(R)(X), x ∈ X) |- ¬(x R x)
  ) {
    assume(irreflexive(R)(X))

    thenHave(∀(x ∈ X, ¬(x R x))) by Substitute(irreflexive.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  //////////////////////////////////////////////////////////////////////////
  section("Properties")

  /**
   * Theorem --- Any irreflexive relation is not reflexive on a non-empty set.
   */
  val `irreflexive ==> ¬reflexive` = Theorem(
    (irreflexive(R)(X), X ≠ ∅) |- ¬(reflexive(R)(X))
  ) {
    assume(irreflexive(R)(X))
    assume(X ≠ ∅)

    have(∀(x ∈ X, ¬(x R x))) by Tautology.from(irreflexive.definition)
    thenHave(x ∈ X ==> ¬(x R x)) by InstantiateForall(x)
    thenHave(x ∈ X |- x ∈ X /\ ¬(x R x)) by Tautology
    thenHave(x ∈ X |- ∃(x, x ∈ X /\ ¬(x R x))) by RightExists
    thenHave(∃(x, x ∈ X) |- ∃(x, x ∈ X /\ ¬(x R x))) by LeftExists

    have(∃(x, x ∈ X /\ ¬(x R x))) by Cut(EmptySet.nonEmptyHasElement of (x := X), lastStep)
    thenHave(thesis) by Tautology.fromLastStep(reflexive.definition)
  }

  /**
   * Theorem --- Any asymmetric relation is irreflexive.
   *
   * The converse holds if `R` is irreflexive (see [[`transitive + irreflexive ==> asymmetric`]]).
   */
  val `asymmetric ==> irreflexive` = Theorem(
    asymmetric(R)(X) |- irreflexive(R)(X)
  ) {
    assume(asymmetric(R)(X))
    have(∀(x ∈ X, ∀(y ∈ X, (x R y) ==> ¬(y R x)))) by Tautology.from(asymmetric.definition)
    thenHave(∀(x, ∀(y, x ∈ X /\ (y ∈ X) /\ (x R y) ==> ¬(y R x)))) by Tableau
    thenHave(x ∈ X /\ (x ∈ X) /\ (x R x) ==> ¬(x R x)) by InstantiateForall(x, x)
    thenHave(x ∈ X ==> ¬(x R x)) by Tautology
    thenHave(∀(x ∈ X, ¬(x R x))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(asymmetric.definition, irreflexive.definition)
  }

  /**
   * Theorem --- Any transitive irreflexive relation `R` is asymmetric.
   *
   * @see [[`asymmetric ==> irreflexive`]]
   */
  val `transitive + irreflexive ==> asymmetric` = Theorem(
    (transitive(R)(X), irreflexive(R)(X)) |- asymmetric(R)(X)
  ) {
    assume(transitive(R)(X))
    assume(irreflexive(R)(X))

    sorry
  }
}
