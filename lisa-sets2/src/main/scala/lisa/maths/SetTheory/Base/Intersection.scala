package lisa.maths.SetTheory.Base

import Comprehension.|
import Union.∪

/** The intersection of two sets `x` and `y` is the `x ∩ y` that contains
  * elements that are common to `x` and `y`.
  *
  * More generally, we can define the intersection of an arbitrary collection of
  * sets `S` as the set `⋂S` of elements of sets of `S` that are in every set of `S`.
  * This definition is such that it coincides with the usual binary intersection
  * for unordered pairs: `⋂{x, y} = x ∩ y` (see [[Intersection.ofUnorderedPair]]).
  */
object Intersection extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val S = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /** Binary Set Intersection --- Intersection of two sets.
    *
    *     `x ∩ y = {z ∈ x | z ∈ y}`
    *
    * @param x set
    * @param y set
    */
  val ∩ = DEF(λ(x, λ(y, { z ∈ x | z ∈ y }))).printInfix()
  val intersection = ∩

  extension (x: set) {

    /** Infix notation for set intersection.
      */
    inline infix def ∩(y: set): set = intersection(x)(y)
  }

  /** Theorem --- An set is a member of the intersection if and only if it is a
    * member of both sets.
    *
    *    `z ∈ x ∩ y <=> z ∈ x /\ z ∈ y`
    */
  val membership = Theorem(
    z ∈ (x ∩ y) <=> (z ∈ x) /\ (z ∈ y)
  ) {
    have(z ∈ { z ∈ x | z ∈ y } <=> (z ∈ x) /\ (z ∈ y)) by Comprehension.apply
    thenHave(thesis) by Substitute(∩.definition)
  }

  /** Theorem --- Set intersection commutes.
    *
    *    `x ∩ y = y ∩ x`
    *
    * This follows from the commutativity of logical conjunction.
    */
  val commutativity = Theorem(
    x ∩ y === y ∩ x
  ) {
    have(z ∈ (x ∩ y) <=> z ∈ (y ∩ x)) by Tautology.from(
      membership of (x := x, y := y),
      membership of (x := y, y := x)
    )
    thenHave(thesis) by Extensionality
  }

  /** Theorem --- If `x ⊆ y` then the intersection is x.
    *
    *    `x ⊆ y ==> x ∩ y = x`
    */
  val ofSubsets = Theorem(
    x ⊆ y |- x ∩ y === x
  ) {
    assume(x ⊆ y)
    have(z ∈ (x ∩ y) <=> z ∈ x) by Tautology.from(membership, Subset.membership)
    thenHave(thesis) by Extensionality
  }

  /** Unary Intersection --- Intersection of all elements of a given set.
    *
    *     `⋂ S = {x ∈ ⋃(S) | ∀y ∈ S. x ∈ y}`
    *
    * @param S set
    */
  val ⋂ = DEF(λ(S, { x ∈ ⋃(S) | ∀(y, y ∈ S ==> x ∈ y) }))
  val unaryIntersection = ⋂

  /** Theorem --- Binary intersection can be formulated using unary intersection.
    *
    *   `x ∩ y = ⋂ {x, y}`
    */
  val ofUnorderedPair = Theorem(
    x ∩ y === ⋂(unorderedPair(x, y))
  ) {
    val LHS = have(z ∈ (x ∩ y) <=> (z ∈ x) /\ (z ∈ y)) by Restate.from(membership)

    val RHS = {
      have(z ∈ { z ∈ ⋃(unorderedPair(x, y)) | ∀(a, a ∈ unorderedPair(x, y) ==> z ∈ a) } <=> (z ∈ ⋃(unorderedPair(x, y))) /\ ∀(a, a ∈ unorderedPair(x, y) ==> z ∈ a)) by Comprehension.apply
      thenHave(z ∈ ⋂(unorderedPair(x, y)) <=> (z ∈ (x ∪ y)) /\ ∀(a, a ∈ unorderedPair(x, y) ==> z ∈ a)) by Substitute(
        ⋂.definition of (S := unorderedPair(x, y)),
        ∪.definition
      )
      thenHave(z ∈ ⋂(unorderedPair(x, y)) <=> (z ∈ x) /\ (z ∈ y)) by Tautology.fromLastStep(
        UnorderedPair.universalQuantifier of (P := λ(a, z ∈ a)),
        Union.membership
      )
    }

    have(z ∈ (x ∩ y) <=> z ∈ ⋂(unorderedPair(x, y))) by Tautology.from(LHS, RHS)
    thenHave(thesis) by Extensionality
  }
}
