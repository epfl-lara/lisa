package lisa.maths.SetTheory.Relations
package Examples

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.*

/** The membership relation on `A` is the relation `∈_A` whose elements are
  * pairs `(x, y)` of elements of `A` such that `x ∈ y`. It views `∈` as a
  * binary set relation in the sense of [[Relations.relation]].
  */
object MembershipRelation extends lisa.Main {

  private val x, y = variable[Ind]
  private val a, b = variable[Ind]
  private val A, B = variable[Ind]
  private val ℛ, X = variable[Ind]

  /** Membership relation --- The membership relation on `A` is the set of pairs
    * `(x, y)` of elements of `A` such that `x ∈ y`.
    *
    *   `∈_A = {(x, y) ∈ (A × A) | x ∈ y}`
    */
  val membershipRelation = DEF(λ(A, { x ∈ (A × A) | fst(x) ∈ snd(x) })).printAs(args => s"∈_${args(0)}")

  /** Theorem --- `(x, y) ∈ ∈_A` if and only if `x ∈ A`, `y ∈ A` and `x ∈ y`.
    *
    *   `(x, y) ∈ ∈_A <=> x ∈ A /\ y ∈ A /\ x ∈ y`
    */
  val membership = Theorem(
    (x, y) ∈ membershipRelation(A) <=> (x ∈ A) /\ (y ∈ A) /\ (x ∈ y)
  ) {
    have((x, y) ∈ { x ∈ (A × A) | fst(x) ∈ snd(x) } <=> (x, y) ∈ (A × A) /\ (fst((x, y)) ∈ snd((x, y)))) by Comprehension.apply
    thenHave(thesis) by Substitute(
      membershipRelation.definition,
      CartesianProduct.pairMembership of (A := A, B := A),
      Pair.pairFst,
      Pair.pairSnd
    )
  }

  /** Theorem --- The membership relation `∈_A` is a relation on `A`.
    */
  val isRelation = Theorem(
    relationOn(membershipRelation(A))(A)
  ) {
    have({ x ∈ (A × A) | fst(x) ∈ snd(x) } ⊆ (A × A)) by Tautology.from(
      Comprehension.subset of (y := (A × A), φ := λ(x, fst(x) ∈ snd(x)))
    )
    thenHave(membershipRelation(A) ⊆ (A × A)) by Substitute(membershipRelation.definition)
    thenHave(thesis) by Substitute(relationOn.definition of (ℛ := membershipRelation(A), X := A))
  }

  /** Theorem --- The membership relation on `A` is irreflexive.
    *
    * Follows from [[WellFounded.selfNonInclusion]].
    */
  val irreflexivity = Theorem(
    irreflexive(membershipRelation(A))
  ) {
    have((x, x) ∈ membershipRelation(A) |- x ∈ x) by Tautology.from(membership of (x := x, y := x))
    thenHave(¬((x, x) ∈ membershipRelation(A))) by Tautology.fromLastStep(WellFounded.selfNonInclusion)
    thenHave(∀(x, ¬((x, x) ∈ membershipRelation(A)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      isRelation,
      Properties.relationOnIsRelation of (ℛ := membershipRelation(A), X := A),
      irreflexive.definition of (ℛ := membershipRelation(A))
    )
  }

  /** Theorem --- The membership relation on the empty set is the empty set.
    */
  val emptySet = Theorem(
    membershipRelation(∅) === ∅
  ) {
    have(membershipRelation(∅) ⊆ (∅ × ∅)) by Tautology.from(
      isRelation of (A := ∅),
      relationOn.definition of (ℛ := membershipRelation(∅), X := ∅)
    )
    thenHave(membershipRelation(∅) ⊆ ∅) by Substitute(CartesianProduct.leftEmpty of (x := ∅))
    thenHave(thesis) by Tautology.fromLastStep(Subset.rightEmpty of (x := membershipRelation(∅)))
  }
}
