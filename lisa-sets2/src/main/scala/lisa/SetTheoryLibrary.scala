package lisa

import lisa.utils.fol.FOL.{_, given}
import lisa.kernel.proof.RunningTheory
import lisa.utils.prooflib.Library

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object SetTheoryLibrary extends lisa.utils.prooflib.Library {

  val theory = new RunningTheory()

  // Predicates
  /**
   * The symbol for the set membership predicate.
   */
  final val in = constant[Ind >>: Ind >>: Prop]("elem")

  /**
   * The symbol for the subset predicate.
   */
  final val subset = constant[Ind >>: Ind >>: Prop]("subsetOf")

  /**
   * The symbol for the equicardinality predicate. Needed for Tarski's axiom.
   */
  final val sim = constant[Ind >>: Ind >>: Prop]("sameCardinality") // Equicardinality
  /**
   * Set Theory basic predicates
   */
  final val predicates = Set(in, subset, sim)
  // val choice

  // Functions
  /**
   * The symbol for the empty set constant.
   */
  final val emptySet = constant[Ind]("emptySet")

  /**
   * The symbol for the unordered pair function.
   */
  final val unorderedPair = constant[Ind >>: Ind >>: Ind]("unorderedPair")

  /**
   * The symbol for the powerset function.
   */
  final val powerSet = constant[Ind >>: Ind]("powerSet")

  /**
   * The symbol for the set union function.
   */
  final val union = constant[Ind >>: Ind]("union")

  /**
   * The symbol for the universe function. Defined in TG set theory.
   */
  final val universe = constant[Ind >>: Ind]("universe")

  /**
   * Set Theory basic functions.
   */
  final val functions = Set(unorderedPair, powerSet, union, universe)

  /**
   * The kernel theory loaded with Set Theory symbols and axioms.
   */
  // val runningSetTheory: RunningTheory = new RunningTheory()
  // given RunningTheory = runningSetTheory

  predicates.foreach(s => addSymbol(s))
  functions.foreach(s => addSymbol(s))
  addSymbol(emptySet)

  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  final val φ = variable[Ind >>: Prop]
  private val A = variable[Ind]
  private val B = variable[Ind]
  private val P = variable[Ind >>: Ind >>: Prop]

  ////////////
  // Axioms //
  ////////////

  // Z
  ////////

  /**
   * Extensionality Axiom --- Two sets are equal iff they have the same
   * elements.
   *
   * `() |- (x = y) ⇔ ∀ z. z ∈ x ⇔ z ∈ y`
   */
  final val extensionalityAxiom: this.AXIOM = Axiom(forall(z, (z ∈ x) <=> (z ∈ y)) <=> (x === y))

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
  final val pairAxiom: AXIOM = Axiom(z ∈ unorderedPair(x, y) <=> (x === z) \/ (y === z))

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
  final val comprehensionSchema: AXIOM = Axiom(exists(y, forall(x, (x ∈ y) <=> ((x ∈ z) /\ φ(x)))))

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
  final val emptySetAxiom: AXIOM = Axiom(!(x ∈ emptySet))

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
  final val unionAxiom: AXIOM = Axiom(z ∈ union(x) <=> exists(y, (y ∈ x) /\ (z ∈ y)))

  /**
   * Subset Axiom --- For sets `x` and `y`, `x` is a subset of `y` iff every
   * element of `x` is in `y`. Denoted `x ⊆ y`.
   *
   * `() |- x ⊆ y ⇔ (z ∈ x ⇒ z ∈ y)`
   *
   * This axiom defines the [[subset]] symbol as this predicate.
   */
  final val subsetAxiom: AXIOM = Axiom((x ⊆ y) <=> forall(z, (z ∈ x) ==> (z ∈ y)))

  /**
   * Power Set Axiom --- For a set `x`, there exists a power set of `x`, denoted
   * `PP(x)` or `power(x)` which contains every subset of x.
   *
   * `() |- z ∈ power(x) ⇔ z ⊆ x`
   *
   * This axiom defines [[powerSet]] as the function symbol representing this
   * set.
   */
  final val powerAxiom: AXIOM = Axiom(x ∈ powerSet(y) <=> x ⊆ y)

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
  final val infinityAxiom: AXIOM = Axiom(exists(x, emptySet ∈ x /\ forall(y, (y ∈ x) ==> union(unorderedPair(y, unorderedPair(y, y))) ∈ x)))

  /**
   * Foundation/Regularity Axiom --- Every non-empty set `x` has an `∈`-minimal
   * element. Equivalently, the relation `∈` on any family of sets is
   * well-founded.
   *
   * `() |- (x != ∅) ==> ∃ y ∈ x. ∀ z. z ∈ x ⇒ ! z ∈ y`
   */
  final val foundationAxiom: AXIOM = Axiom(!(x === emptySet) ==> exists(y, (y ∈ x) /\ forall(z, (z ∈ x) ==> !(z ∈ y))))

  // ZF
  /////////

  /**
   * Replacement Schema --- If a predicate `P` is 'functional' over `x`, i.e.,
   * given `a ∈ x`, there is a unique `b` such that `P(x, a, b)`, then the
   * 'image' of `x` in P exists and is a set. It contains exactly the `b`'s that
   * satisfy `P` for each `a ∈ x`.
   */
  final val replacementSchema: AXIOM = Axiom(
    forall(x, (x ∈ A) ==> ∀(y, ∀(z, (P(x)(y) /\ P(x)(z)) ==> (y === z)))) ==>
      exists(B, forall(y, (y ∈ B) <=> exists(x, (x ∈ A) /\ P(x)(y))))
  )

  final val tarskiAxiom: AXIOM = Axiom(
    forall(
      x,
      (x ∈ universe(x)) /\
        forall(
          y,
          (y ∈ universe(x)) ==> ((powerSet(y) ∈ universe(x)) /\ (powerSet(y) ⊆ universe(x))) /\
            forall(z, (z ⊆ universe(x)) ==> (sim(y)(universe(x)) /\ (y ∈ universe(x))))
        )
    )
  )

  /**
   * The set of all axioms of Tarski-Grothedick (TG) set theory.
   *
   * @return
   */
  def axioms: Set[(String, AXIOM)] = Set(
    ("EmptySet", emptySetAxiom),
    ("extensionalityAxiom", extensionalityAxiom),
    ("pairAxiom", pairAxiom),
    ("unionAxiom", unionAxiom),
    ("subsetAxiom", subsetAxiom),
    ("powerAxiom", powerAxiom),
    ("foundationAxiom", foundationAxiom),
    ("infinityAxiom", infinityAxiom),
    ("comprehensionSchema", comprehensionSchema),
    ("replacementSchema", replacementSchema),
    ("TarskiAxiom", tarskiAxiom)
  )

  /////////////
  // Aliases //
  /////////////

  // Unicode symbols

  val ∅ = emptySet
  val ∈ = in

  extension (l: Expr[Ind])
    def ∈(r: Expr[Ind]): Expr[Prop] = in(l)(r)
    def ⊆(r: Expr[Ind]): Expr[Prop] = subset(l)(r)

  def unorderedPair(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = App(App(unorderedPair, x), y)

}
