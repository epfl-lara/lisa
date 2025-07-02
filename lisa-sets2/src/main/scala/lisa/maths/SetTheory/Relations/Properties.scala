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

  /** Theorem --- If `ℛ` is a relation, then `ℛ ⊆ dom(ℛ) × range(ℛ)`.
    *
    *   `relation(ℛ) |- ℛ ⊆ dom(ℛ) × range(ℛ)`
    */
  val relationDomainRange = Theorem(
    relation(ℛ) |- ℛ ⊆ (dom(ℛ) × range(ℛ))
  ) {
    sorry
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

  /*
  /**
   * Theorem --- The union of a set of relations is a relation itself.
   *
   *    `∀ ℛ ∈ x. relation(ℛ, X) |- relation(⋃x, X)
   *
   */
  val unionOfRelations = Theorem(
    ∀(ℛ, ℛ ∈ x ==> relation(ℛ)(X)) |- relation(⋃(x))(X)
  ) {
    assume(∀(ℛ, ℛ ∈ x ==> relation(ℛ)(X)))
    val isRelation = thenHave(y ∈ x ==> relation(y)(X)) by InstantiateForall(y)

    have(z ∈ ⋃(x) |- ∃(y, (y ∈ x) /\ (z ∈ y))) by Tautology.from(unionAxiom)

    thenHave((y ∈ x) /\ (z ∈ y) |- relation(y)(X) /\ (z ∈ y)) by Tautology.fromLastStep(isRelation)
    // thenHave((y ∈ x) /\ (z ∈ y) |- relation(y)(X) /\ (z ∈ (X × X))) by Tautology.fromLastStep(isRelation)
    sorry
    /*
    // union of a set of relations contains only pairs
    have(forall(t, in(t, z) ==> relation(t)) |- forall(t, in(t, union(z)) ==> exists(a, exists(b, (t === pair(a, b)))))) subproof {
      assume(forall(t, in(t, z) ==> relation(t)))
      have(in(x, z) ==> relation(x)) by InstantiateForall
      have(in(x, z) |- forall(t, in(t, x) ==> exists(a, exists(b, (t === pair(a, b)))))) by Tautology.from(lastStep, setOfPairsIsRelation of z -> x)
      thenHave((in(x, z) /\ in(t, x)) |- exists(a, exists(b, (t === pair(a, b))))) by InstantiateForall(t)
      thenHave(exists(x, in(x, z) /\ in(t, x)) |- exists(a, exists(b, (t === pair(a, b))))) by LeftExists

      have(in(t, union(z)) ==> exists(a, exists(b, (t === pair(a, b))))) by Tautology.from(lastStep, unionAxiom of (x -> z, z -> t))
      thenHave(thesis) by RightForall
    }

    // a set of pairs is a relation
    have(thesis) by Tautology.from(lastStep, setOfPairsIsRelation of z -> union(z))
   */
  }

   */

  /** TODO: Add closures. */
}
