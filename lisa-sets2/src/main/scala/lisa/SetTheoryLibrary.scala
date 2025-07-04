package lisa

import lisa.utils.fol.FOL.{_, given}
import lisa.kernel.proof.RunningTheory
import lisa.utils.prooflib.Library

import scala.annotation.showAsInfix

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object SetTheoryLibrary extends lisa.utils.prooflib.Library {

  val theory = new RunningTheory()

  /** Terms in set theory represent sets. */
  type set = Expr[Ind]

  // Predicates

  /**
   * The symbol for the set membership predicate.
   */
  object ∈ extends Constant[Ind >>: Ind >>: Prop]("∈") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(set, set)] =
      val ∈ = this
      e match
        case App(App(`∈`, x), y) => Some(x, y)
        case _ => None
  }

  extension (x: set) {
    inline infix def ∈(y: set): Expr[Prop] = App(App(SetTheoryLibrary.∈, x), y)
    inline infix def ∉(y: set): Expr[Prop] = !(x ∈ y)
  }

  /**
   * The symbol for the subset predicate.
   */
  object ⊆ extends Constant[Ind >>: Ind >>: Prop]("⊆") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(set, set)] =
      val ⊆ = this
      e match
        case App(App(`⊆`, x), y) => Some(x, y)
        case _ => None
  }

  extension (x: set) {
    inline infix def ⊆(y: set): Expr[Prop] = App(App(SetTheoryLibrary.⊆, x), y)
  }

  /**
   * The symbol for the equicardinality predicate. Needed for Tarski's axiom.
   */
  final val sim = constant[Ind >>: Ind >>: Prop]("sameCardinality") // Equicardinality

  /**
   * Set Theory basic predicates
   */
  final val predicates = Set(∈, ⊆, sim)

  // Functions

  /**
   * The symbol for the empty set constant.
   */
  final val ∅ = constant[Ind]("∅")

  /**
   * The symbol for the unordered pair function.
   */
  final val unorderedPair = constant[Ind >>: Ind >>: Ind]("unorderedPair").printAs(args => s"{${args(0)}, ${args(1)}}")

  /**
   * The symbol for the powerset function.
   */
  final val 𝒫 = constant[Ind >>: Ind]("𝒫")

  /**
   * The symbol for the set union function.
   */
  final val ⋃ = constant[Ind >>: Ind]("⋃")

  /**
   * The symbol for the universe function. Defined in TG set theory.
   */
  final val universe = constant[Ind >>: Ind]("universe")

  /**
   * Set Theory basic functions.
   */
  final val functions = Set(unorderedPair, 𝒫, ⋃, universe)

  /**
   * The kernel theory loaded with Set Theory symbols and axioms.
   */
  // val runningSetTheory: RunningTheory = new RunningTheory()
  // given RunningTheory = runningSetTheory

  predicates.foreach(s => addSymbol(s))
  functions.foreach(s => addSymbol(s))
  addSymbol(∅)

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
   * `() |- x = y ⇔ ∀ z. z ∈ x ⇔ z ∈ y`
   */
  final val extensionalityAxiom: this.AXIOM = Axiom(∀(z, z ∈ x <=> z ∈ y) <=> (x === y))

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
  final val pairAxiom: AXIOM = Axiom(z ∈ unorderedPair(x, y) <=> (z === x) \/ (z === y))

  /**
   * Comprehension/Separation Schema --- For a formula `ϕ(_, _)` and a set `y`,
   * there exists a set `z` which contains only the elements `x` of `y` that
   * satisfy `ϕ(x, y)`. This is represented mathematically as `z = {x ∈ y | ϕ(x,
   * y)}`.
   *
   * `() |- ∃ z. ∀ x. x ∈ z ⇔ (x ∈ y ∧ ϕ(x, y))`
   *
   * This schema represents an infinite collection of axioms, one for each
   * formula `ϕ(x, y)`.
   */
  final val comprehensionSchema: AXIOM = Axiom(∃(z, ∀(x, x ∈ z <=> (x ∈ y) /\ φ(x))))

  /**
   * Empty Set Axiom --- From the Comprehension Schema follows the existence of
   * a set containing no elements, the empty set.
   *
   * `∅ = {x ∈ X | x ≠ x}`
   *
   * This axiom defines [[emptySet]] as the constant symbol representing this set.
   *
   * `() |- x ∉ ∅`
   */
  final val emptySetAxiom: AXIOM = Axiom(x ∉ ∅)

  /**
   * Union Axiom --- For any set `x`, there exists a set `⋃x` which is the
   * union of its elements. For every element of `⋃x`, there is an element
   * `y` of `x` which contains it.
   *
   * `() |- z ∈ ⋃(x) ⇔ ∃ y. y ∈ x ∧ z ∈ y`
   *
   * This axiom defines [[union]] as the function symbol representing this set.
   */
  final val unionAxiom: AXIOM = Axiom(z ∈ ⋃(x) <=> ∃(y, (y ∈ x) /\ (z ∈ y)))

  /**
   * Subset Axiom --- For sets `x` and `y`, `x` is a subset of `y` iff every
   * element of `x` is in `y`. Denoted `x ⊆ y`.
   *
   * `() |- x ⊆ y ⇔ (z ∈ x ⇒ z ∈ y)`
   *
   * This axiom defines the [[subset]] symbol as this predicate.
   */
  final val subsetAxiom: AXIOM = Axiom((x ⊆ y) <=> ∀(z, (z ∈ x) ==> (z ∈ y)))

  /**
   * Power Set Axiom --- For a set `x`, there exists a power set of `x`, denoted
   * `𝒫(x)` or `power(x)` which contains every subset of x.
   *
   * `() |- z ∈ 𝒫(x) ⇔ z ⊆ x`
   *
   * This axiom defines [[𝒫]] as the function symbol representing this
   * set.
   */
  final val powerSetAxiom: AXIOM = Axiom(x ∈ 𝒫(y) <=> x ⊆ y)

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
  final val infinityAxiom: AXIOM = Axiom(∃(x, ∅ ∈ x /\ ∀(y, (y ∈ x) ==> ⋃(unorderedPair(y, unorderedPair(y, y))) ∈ x)))

  /**
   * Foundation/Regularity Axiom --- Every non-empty set `x` has an `∈`-minimal
   * element. Equivalently, the relation `∈` on any family of sets is
   * well-founded.
   *
   * `() |- x ≠ ∅ ==> ∃ y ∈ x. ∀ z. z ∈ x ⇒ z ∉ y`
   */
  final val axiomOfFoundation: AXIOM = Axiom(x ≠ ∅ ==> ∃(y, (y ∈ x) /\ ∀(z, z ∈ x ==> z ∉ y)))

  // ZF
  /////////

  /**
   * Replacement Schema --- If a predicate `P` is 'functional' over `x`, i.e.,
   * given `a ∈ x`, there is a unique `b` such that `P(x, a, b)`, then the
   * 'image' of `x` in P exists and is a set. It contains exactly the `b`'s that
   * satisfy `P` for each `a ∈ x`.
   */
  final val replacementSchema: AXIOM = Axiom(
    ∀(x, x ∈ A ==> ∀(y, ∀(z, P(x)(y) /\ P(x)(z) ==> (y === z)))) ==>
      ∃(B, ∀(y, y ∈ B <=> ∃(x, (x ∈ A) /\ P(x)(y))))
  )

  // TG
  /////////

  final val tarskiAxiom: AXIOM = Axiom(
    ∀(x, (x ∈ universe(x)) /\
      ∀(y,
        (y ∈ universe(x)) ==> ((𝒫(y) ∈ universe(x)) /\ (𝒫(y) ⊆ universe(x))) /\
          ∀(z, (z ⊆ universe(x)) ==> (sim(y)(universe(x)) /\ (y ∈ universe(x))))
      )
    )
  )

  /** Zermelo set theory axioms. */
  val Z = Set(
    emptySetAxiom,
    extensionalityAxiom,
    comprehensionSchema,
    pairAxiom,
    unionAxiom,
    infinityAxiom,
    powerSetAxiom,
    axiomOfFoundation
  )

  /** Zermelo-Frankel set theory axioms. */
  val ZF = Z + replacementSchema

  /** ZF with the axiom of choice. */
  // val ZFC = ZF + axiomOfChoice

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
    ("powerSetAxiom", powerSetAxiom),
    ("axiomOfFoundation", axiomOfFoundation),
    ("infinityAxiom", infinityAxiom),
    ("comprehensionSchema", comprehensionSchema),
    ("replacementSchema", replacementSchema),
    ("TarskiAxiom", tarskiAxiom)
  )

  ///////////////
  // Notations //
  ///////////////

  def unorderedPair(x: set, y: set): set = App(App(unorderedPair, x), y)

  /*
  private val db = HintDatabase.empty
  given HintDatabase = db

  export lisa.simplifyHint
  val Simplify = lisa.automation.Simplify(using db)
   */
}
