package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.KernelHelpers.{_, given}

/**
 * Axioms for the Zermelo theory (Z)
 */
private[settheory] trait SetTheoryZAxioms extends SetTheoryDefinitions {

  private val (x, y, z) =
    (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))
  final val sPhi = SchematicPredicateLabel("P", 2)

  /**
   * Extensionality Axiom --- Two sets are equal iff they have the same
   * elements.
   *
   * `() |- (x = y) ⇔ ∀ z. z ∈ x ⇔ z ∈ y`
   */
  final val extensionalityAxiom: Formula = forall(z, in(z, x) <=> in(z, y)) <=> (x === y)

  /**
   * Pairing Axiom --- For any sets `x` and `y`, there is a set that contains
   * exactly `x` and `y`. This set is denoted mathematically as `{x, y}` and
   * here as `unorderedPair(x, y)`.
   *
   * `() |- z ∈ {x, y} ⇔ (z === x ∨ z === y)`
   *
   * This axiom defines [[unorderedPair]] as the function symbol representing
   * this set.
   */
  final val pairAxiom: Formula = in(z, unorderedPair(x, y)) <=> (x === z) \/ (y === z)

  /**
   * Comprehension/Separation Schema --- For a formula `ϕ(_, _)` and a set `z`,
   * there exists a set `y` which contains only the elements `x` of `z` that
   * satisfy `ϕ(x, z)`. This is represented mathematically as `y = {x ∈ z | ϕ(x,
   * z)}`.
   *
   * `() |- ∃ y. ∀ x. x ∈ y ⇔ (x ∈ z ∧ ϕ(x, z))`
   *
   * This schema represents an infinite collection of axioms, one for each
   * formula `ϕ(x, z)`.
   */
  final val comprehensionSchema: Formula = exists(y, forall(x, in(x, y) <=> (in(x, z) /\ sPhi(x, z))))

  /**
   * Empty Set Axiom --- From the Comprehension Schema follows the existence of
   * a set containing no elements, the empty set.
   *
   * `∅ = {x ∈ X | x != x}`.
   *
   * This axiom defines [[emptySet]] as the constant symbol representing this set.
   *
   * `() |- !(x ∈ ∅)`
   */
  final val emptySetAxiom: Formula = !in(x, emptySet())

  /**
   * Union Axiom --- For any set `x`, there exists a set `union(x)` which is the
   * union of its elements. For every element of `union(x)`, there is an element
   * `y` of `x` which contains it.
   *
   * `() |- z ∈ union(x) ⇔ ∃ y. y ∈ x ∧ z ∈ y`
   *
   * Mathematically, we write `union(x)` as `∪ x`.
   *
   * This axiom defines [[union]] as the function symbol representing this set.
   */
  final val unionAxiom: Formula = in(x, union(z)) <=> exists(y, in(x, y) /\ in(y, z))

  /**
   * Subset Axiom --- For sets `x` and `y`, `x` is a subset of `y` iff every
   * element of `x` is in `y`. Denoted `x ⊆ y`.
   *
   * `() |- x ⊆ y ⇔ (z ∈ x ⇒ z ∈ y)`
   *
   * This axiom defines the [[subset]] symbol as this predicate.
   */
  final val subsetAxiom: Formula = subset(x, y) <=> forall(z, in(z, x) ==> in(z, y))

  /**
   * Power Set Axiom --- For a set `x`, there exists a power set of `x`, denoted
   * `PP(x)` or `power(x)` which contains every subset of x.
   *
   * `() |- z ∈ power(x) ⇔ z ⊆ x`
   *
   * This axiom defines [[powerSet]] as the function symbol representing this
   * set.
   */
  final val powerAxiom: Formula = in(x, powerSet(y)) <=> subset(x, y)

  /**
   * Infinity Axiom --- There exists an infinite set.
   *
   * The definition requires a notion of finiteness, which generally corresponds
   * to natural numbers. Since the naturals have not yet been defined, their
   * definition and structure is imitated in the definition of an inductive set.
   *
   * `inductive(x) ⇔ (∅ ∈ x ∧ ∀ y. y ∈ x ⇒ y ∪ {y} ∈ x)`
   *
   * This axiom postulates that there exists an inductive set.
   *
   * `() |- ∃ x. inductive(x)`
   */
  final val infinityAxiom: Formula = exists(x, in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)))

  /**
   * Foundation/Regularity Axiom --- Every non-empty set `x` has an `∈`-minimal
   * element. Equivalently, the relation `∈` on any family of sets is
   * well-founded.
   *
   * `() |- (x != ∅) ==> ∃ y ∈ x. ∀ z. z ∈ x ⇒ ! z ∈ y`
   */
  final val foundationAxiom: Formula = !(x === emptySet()) ==> exists(y, in(y, x) /\ forall(z, in(z, x) ==> !in(z, y)))

  private val zAxioms: Set[(String, Formula)] = Set(
    ("EmptySet", emptySetAxiom),
    ("extensionalityAxiom", extensionalityAxiom),
    ("pairAxiom", pairAxiom),
    ("unionAxiom", unionAxiom),
    ("subsetAxiom", subsetAxiom),
    ("powerAxiom", powerAxiom),
    ("foundationAxiom", foundationAxiom),
    ("infinityAxiom", infinityAxiom),
    ("comprehensionSchema", comprehensionSchema)
  )

  zAxioms.foreach(a => runningSetTheory.addAxiom(a._1, a._2))

  override def axioms: Set[(String, Formula)] = super.axioms ++ zAxioms

}
