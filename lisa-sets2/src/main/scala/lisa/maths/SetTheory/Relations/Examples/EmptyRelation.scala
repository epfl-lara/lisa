package lisa.maths.SetTheory.Relations.Examples

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.*

/** The empty relation is the relation that relates no elements together, i.e.,
  * it is defined as the empty set.
  */
object EmptyRelation extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val ℛ = variable[Ind]
  private val X = variable[Ind]

  /** Theorem --- The empty set is a relation on any set `X`. It is called the
    * empty relation.
    */
  val emptyRelation = Theorem(
    relationOn(∅)(X)
  ) {
    have(thesis) by Tautology.from(
      relationOn.definition of (ℛ := ∅),
      Subset.leftEmpty of (x := X × X)
    )
  }

  /** Theorem --- The empty relation has an empty domain.
    */
  val emptyRelationDomain = Theorem(
    dom(∅) === ∅
  ) {
    have(x ∈ { x ∈ ⋃(⋃(∅)) | ∃(y, (x, y) ∈ ∅) } <=> (x ∈ ⋃(⋃(∅))) /\ (∃(y, (x, y) ∈ ∅))) by Tautology.from(
      Comprehension.membership of (y := ⋃(⋃(∅)), φ := λ(x, ∃(y, (x, y) ∈ ∅)))
    )
    // thenHave(x ∈ dom(∅) <=> (x ∈ ⋃(⋃(∅))) /\ (∃(y, (x, y) ∈ ∅))) by Substitute(dom.definition of (ℛ := ∅))
    sorry
  }

  /** Theorem --- The empty relation has an empty range.
    */
  val emptyRelationRange = Theorem(
    range(∅) === ∅
  ) {
    sorry
  }

  /** Theorem --- The empty relation on the empty set is reflexive.
    */
  val emptyRelationReflexive = Theorem(
    reflexive(∅)(∅)
  ) {
    have(x ∈ ∅ ==> (x, x) ∈ ∅) by Tautology.from(EmptySet.definition)
    thenHave(∀(x, x ∈ ∅ ==> (x, x) ∈ ∅)) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      reflexive.definition of (ℛ := ∅, X := ∅),
      emptyRelation of (X := ∅)
    )
  }

  /** Theorem --- The empty relation is symmetric.
    */
  val emptyRelationSymmetric = Theorem(
    symmetric(∅)
  ) {
    have((x, y) ∈ ∅ <=> (y, x) ∈ ∅) by Tautology.from(
      EmptySet.definition of (x := (x, y)),
      EmptySet.definition of (x := (y, x))
    )
    thenHave(∀(x, ∀(y, (x, y) ∈ ∅ <=> (y, x) ∈ ∅))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      symmetric.definition of (ℛ := ∅),
      emptyRelation,
      Properties.relationOnIsRelation of (ℛ := ∅)
    )
  }

  /** Theorem --- The empty relation is irreflexive.
    */
  val emptyRelationIrreflexive = Theorem(
    irreflexive(∅)
  ) {
    have((x, x) ∉ ∅) by Tautology.from(EmptySet.definition of (x := (x, x)))
    thenHave(∀(x, (x, x) ∉ ∅)) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      irreflexive.definition of (ℛ := ∅),
      emptyRelation,
      Properties.relationOnIsRelation of (ℛ := ∅)
    )
  }

  /** Theorem --- The empty relation is transitive.
    */
  val emptyRelationTransitive = Theorem(
    transitive(∅)
  ) {
    have(((x, y) ∈ ∅) /\ ((y, z) ∈ ∅) ==> (x, z) ∈ ∅) by Tautology.from(EmptySet.definition of (x := (x, y)))
    thenHave(∀(x, ∀(y, ∀(z, ((x, y) ∈ ∅) /\ ((y, z) ∈ ∅) ==> (x, z) ∈ ∅)))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      transitive.definition of (ℛ := ∅),
      emptyRelation,
      Properties.relationOnIsRelation of (ℛ := ∅)
    )
  }

  /** Theorem --- The empty relation is an equivalence relation on the empty set.
    */
  val emptyRelationEquivalence = Theorem(
    equivalence(∅)(∅)
  ) {
    have(thesis) by Tautology.from(
      equivalence.definition of (ℛ := ∅, X := ∅),
      emptyRelationReflexive,
      emptyRelationSymmetric,
      emptyRelationTransitive
    )
  }

  /** Theorem --- The empty relation is anti-symmetric.
    */
  val emptyRelationAntisymmetric = Theorem(
    antisymmetric(∅)
  ) {
    have(((x, y) ∈ ∅) /\ ((y, x) ∈ ∅) ==> (x === y)) by Tautology.from(EmptySet.definition of (x := (x, y)))
    thenHave(∀(x, ∀(y, ((x, y) ∈ ∅) /\ ((y, x) ∈ ∅) ==> (x === y)))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      antisymmetric.definition of (ℛ := ∅),
      emptyRelation,
      Properties.relationOnIsRelation of (ℛ := ∅)
    )
  }

  /** Theorem --- The empty relation is asymmetric.
    */
  val emptyRelationAsymmetric = Theorem(
    asymmetric(∅)
  ) {
    have((x, y) ∈ ∅ ==> (y, x) ∉ ∅) by Tautology.from(EmptySet.definition of (x := (x, y)))
    thenHave(∀(x, ∀(y, (x, y) ∈ ∅ ==> (y, x) ∉ ∅))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      asymmetric.definition of (ℛ := ∅),
      emptyRelation,
      Properties.relationOnIsRelation of (ℛ := ∅)
    )
  }

  /** Theorem --- The empty relation is total on the empty set.
    */
  val emptyRelationTotal = Theorem(
    total(∅)(∅)
  ) {
    have((x ∈ ∅) /\ (y ∈ ∅) ==> ((x, y) ∈ ∅) \/ ((y, x) ∈ ∅) \/ (x === y)) by Tautology.from(EmptySet.definition)
    thenHave(∀(x, ∀(y, (x ∈ ∅) /\ (y ∈ ∅) ==> ((x, y) ∈ ∅) \/ ((y, x) ∈ ∅) \/ (x === y)))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      total.definition of (ℛ := ∅, X := ∅),
      emptyRelation of (X := ∅)
    )
  }
}
