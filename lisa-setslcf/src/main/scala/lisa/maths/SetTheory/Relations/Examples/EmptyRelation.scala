package lisa.maths.SetTheory.Relations
package Examples

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Predef._

/**
 * The empty relation is the relation that relates no elements together, i.e.,
 * it is defined as the empty set.
 */
object EmptyRelation extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val R, ~ = variable[Ind]
  private val X = variable[Ind]

  /**
   * Theorem --- The empty set is a relation on any set `X`. It is called the
   * empty relation.
   */
  val emptyRelation = Theorem(
    relationOn(∅)(X)
  ) {
    have(thesis) by Tautology.from(
      relationOn.definition of (R := ∅),
      Subset.leftEmpty of (x := X × X)
    )
  }

  /**
   * Theorem --- The empty relation has an empty domain.
   */
  val emptyDomain = Theorem(
    dom(∅) === ∅
  ) {
    have(z ∈ { fst(z) | z ∈ ∅ } <=> ∃(x ∈ ∅, fst(x) === z)) by Replacement.apply
    thenHave(z ∈ dom(∅) <=> ∃(x ∈ ∅, fst(x) === z)) by Substitute(dom.definition of (R := ∅))
    thenHave(z ∈ dom(∅) <=> z ∈ ∅) by Tautology.fromLastStep(
      EmptySet.existentialQuantifier of (P := λ(x, fst(x) === z)),
      EmptySet.definition of (x := z)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The empty relation has an empty range.
   */
  val emptyRange = Theorem(
    range(∅) === ∅
  ) {
    have(z ∈ { snd(z) | z ∈ ∅ } <=> ∃(x ∈ ∅, snd(x) === z)) by Replacement.apply
    thenHave(z ∈ range(∅) <=> ∃(x ∈ ∅, snd(x) === z)) by Substitute(range.definition of (R := ∅))
    thenHave(z ∈ range(∅) <=> z ∈ ∅) by Tautology.fromLastStep(
      EmptySet.existentialQuantifier of (P := λ(x, snd(x) === z)),
      EmptySet.definition of (x := z)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The empty relation on the empty set is reflexive.
   */
  val emptyRelationReflexive = Theorem(
    reflexive(∅)(∅)
  ) {
    have(x ∈ ∅ ==> (x, x) ∈ ∅) by Tautology.from(EmptySet.definition)
    thenHave(∀(x, x ∈ ∅ ==> (x, x) ∈ ∅)) by RightForall
    thenHave(thesis) by Substitute(reflexive.definition of (R := ∅, X := ∅))
  }

  /**
   * Theorem --- The empty relation is symmetric.
   */
  val emptyRelationSymmetric = Theorem(
    symmetric(∅)(X)
  ) {
    have((x ∈ X) /\ (y ∈ X) ==> ((x, y) ∈ ∅ <=> (y, x) ∈ ∅)) by Tautology.from(
      EmptySet.definition of (x := (x, y)),
      EmptySet.definition of (x := (y, x))
    )
    thenHave(∀(x, ∀(y, (x ∈ X) /\ (y ∈ X) ==> ((x, y) ∈ ∅ <=> (y, x) ∈ ∅)))) by Generalize
    thenHave(∀(x ∈ X, ∀(y ∈ X, ((x, y) ∈ ∅ <=> (y, x) ∈ ∅)))) by Tableau
    thenHave(thesis) by Substitute(symmetric.definition of (R := ∅))
  }

  /**
   * Theorem --- The empty relation is irreflexive.
   */
  val emptyRelationIrreflexive = Theorem(
    irreflexive(∅)(X)
  ) {
    have(x ∈ X ==> (x, x) ∉ ∅) by Tautology.from(EmptySet.definition of (x := (x, x)))
    thenHave(∀(x, x ∈ X ==> (x, x) ∉ ∅)) by RightForall
    thenHave(thesis) by Substitute(irreflexive.definition of (R := ∅))
  }

  /**
   * Theorem --- The empty relation is transitive.
   */
  val emptyRelationTransitive = Theorem(
    transitive(∅)(X)
  ) {
    have((x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ ((x, y) ∈ ∅) /\ ((y, z) ∈ ∅) ==> (x, z) ∈ ∅) by Tautology.from(EmptySet.definition of (x := (x, y)))
    thenHave(∀(x, ∀(y, ∀(z, (x ∈ X) /\ (y ∈ X) /\ (z ∈ X) /\ ((x, y) ∈ ∅) /\ ((y, z) ∈ ∅) ==> (x, z) ∈ ∅)))) by Generalize
    thenHave(∀(x ∈ X, ∀(y ∈ X, ∀(z ∈ X, ((x, y) ∈ ∅) /\ ((y, z) ∈ ∅) ==> (x, z) ∈ ∅)))) by Tableau
    thenHave(thesis) by Substitute(transitive.definition of (R := ∅))
  }

  /**
   * Theorem --- The empty relation is an equivalence relation on the empty set.
   */
  val emptyRelationEquivalence = Theorem(
    equivalence(∅)(∅)
  ) {
    have(thesis) by Tautology.from(
      equivalence.definition of (`~` := ∅, X := ∅),
      emptyRelation of (X := ∅),
      emptyRelationReflexive,
      emptyRelationSymmetric of (X := ∅),
      emptyRelationTransitive of (X := ∅)
    )
  }

  /**
   * Theorem --- The empty relation is anti-symmetric.
   */
  val emptyRelationAntisymmetric = Theorem(
    antisymmetric(∅)(X)
  ) {
    have(((x, y) ∈ ∅) /\ ((y, x) ∈ ∅) ==> (x === y)) by Tautology.from(EmptySet.definition of (x := (x, y)))
    thenHave(∀(x, ∀(y, ((x, y) ∈ ∅) /\ ((y, x) ∈ ∅) ==> (x === y)))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      antisymmetric.definition of (R := ∅),
      emptyRelation,
      BasicTheorems.relationOnIsRelation of (R := ∅)
    )
  }

  /**
   * Theorem --- The empty relation is asymmetric.
   */
  val emptyRelationAsymmetric = Theorem(
    asymmetric(∅)(X)
  ) {
    have((x, y) ∈ ∅ ==> (y, x) ∉ ∅) by Tautology.from(EmptySet.definition of (x := (x, y)))
    thenHave(∀(x, ∀(y, (x, y) ∈ ∅ ==> (y, x) ∉ ∅))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      asymmetric.definition of (R := ∅),
      emptyRelation,
      BasicTheorems.relationOnIsRelation of (R := ∅)
    )
  }

  /**
   * Theorem --- The empty relation is total on the empty set.
   */
  val emptyRelationTotal = Theorem(
    total(∅)(∅)
  ) {
    have((x ∈ ∅) /\ (y ∈ ∅) ==> ((x, y) ∈ ∅) \/ ((y, x) ∈ ∅) \/ (x === y)) by Tautology.from(EmptySet.definition)
    thenHave(∀(x, ∀(y, (x ∈ ∅) /\ (y ∈ ∅) ==> ((x, y) ∈ ∅) \/ ((y, x) ∈ ∅) \/ (x === y)))) by Generalize
    thenHave(∀(x ∈ ∅, ∀(y ∈ ∅, ((x, y) ∈ ∅) \/ ((y, x) ∈ ∅) \/ (x === y)))) by Tableau
    thenHave(thesis) by Substitute(total.definition of (R := ∅, X := ∅))
  }
}
