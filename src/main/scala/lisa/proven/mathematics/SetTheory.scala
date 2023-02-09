package lisa.proven.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.proven.mathematics.SetTheoryTactics.*
import lisa.utils.Printer

/**
 * Set Theory Library
 *
 * Develops Zermelo-Fraenkel Set Theory.
 * Uses the following book as the main reference:
 *
 * Jech, Thomas. Set theory: The third millennium edition, revised and expanded.
 * Springer Berlin Heidelberg, 2003.
 * [[https://link.springer.com/book/10.1007/3-540-44761-X]]
 */
object SetTheory extends lisa.Main {

  // var defs
  private val w = variable
  private val x = variable
  private val y = variable
  private val z = variable
  private val h = formulaVariable
  private val t = variable
  private val a = variable
  private val b = variable
  private val c = variable
  private val d = variable

  // relation and function symbols
  private val r = variable
  private val f = variable
  private val g = variable

  private val P = predicate(1)
  private val Q = predicate(1)
  private val schemPred = predicate(1)

  /**
   * Chapter 1
   */

  /**
   * Axioms of Set Theory
   *
   * See [[SetTheoryZAxioms]] and [[SetTheoryZFAxioms]]
   */

  /**
   * Theorems about basic sets
   */

  /**
   * Theorem --- Russel's Paradox
   *
   * Consider a set `x`, that contains every set that is not a member of itself.
   * The existence of `x` leads to a contradiction. This paradox forces the
   * current form of the comprehension schema, i.e. `{x ∈ X | Ψ(x, X)}`
   * instead of the full comprehension schema `{x | Ψ(x)}`.
   */
  val russelsParadox = makeTHM(
    exists(x, forall(y, !in(y, y) <=> in(y, x))) |- ()
  ) {
    val contra = !in(x, x) <=> in(x, x)

    have(contra |- ()) by Restate
    thenHave(forall(y, !in(y, y) <=> in(y, x)) |- ()) by LeftForall(x)
    thenHave(exists(x, forall(y, !in(y, y) <=> in(y, x))) |- ()) by LeftExists
  }

  /**
   * Theorem --- Uniqueness by Definition
   *
   * If a set is defined by its elements, existence implies uniqueness.
   *
   *    `∃ z. ∀ t. t ∈ z ⇔ P(t) ⊢ ∃! z. ∀ t. t ∈ z ⇔ P(t)`
   *
   * where `P(t)` does not contain `z` as a free variable.
   *
   * @example {{{
   * have(exists(z, forall(t, in(t, z) ⇔ myProperty(t))) ⊢ existsOne(z, forall(t, in(t, z) ⇔ myProperty(t)))) by InstPredSchema(Map(schemPred -> (t, myProperty(t))))`
   * }}}
   *
   * Instantiation will fail if `myProperty(t)` contains `z` as a free variable.
   */
  val uniqueByExtension = makeTHM(
    exists(z, forall(t, in(t, z) <=> schemPred(t))) |- existsOne(z, forall(t, in(t, z) <=> schemPred(t)))
  ) {
    def prop(z: Term) = in(t, z) <=> schemPred(t)
    def fprop(z: Term) = forall(t, prop(z))

    // forward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    thenHave(fprop(z) /\ (z === a) |- fprop(z)) by Weakening
    thenHave(Set(fprop(z) /\ (z === a), (z === a)) |- fprop(a)) by RightSubstEq(List((z, a)), lambda(Seq(z), fprop(z)))
    val forward = thenHave(fprop(z) |- (z === a) ==> fprop(a)) by Restate

    // backward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    val instLhs = thenHave(fprop(z) |- prop(z)) by InstantiateForall(t)
    val instRhs = thenHave(fprop(a) |- prop(a)) by InstFunSchema(Map(z -> a))

    have(Set(fprop(z), fprop(a)) |- prop(z) /\ prop(a)) by RightAnd(instLhs, instRhs)
    thenHave(fprop(z) /\ fprop(a) |- in(t, a) <=> in(t, z)) by Trivial
    val extLhs = thenHave(fprop(z) /\ fprop(a) |- forall(t, in(t, a) <=> in(t, z))) by RightForall
    val extRhs = have(() |- forall(t, in(t, a) <=> in(t, z)) <=> (a === z)) by InstFunSchema(Map(x -> a, y -> z))(extensionalityAxiom)

    have(fprop(z) /\ fprop(a) |- (forall(t, in(t, a) <=> in(t, z)) <=> (a === z)) /\ forall(t, in(t, a) <=> in(t, z))) by RightAnd(extLhs, extRhs)
    thenHave(fprop(z) /\ fprop(a) |- (a === z)) by Trivial
    val backward = thenHave(fprop(z) |- fprop(a) ==> (a === z)) by Restate

    have(fprop(z) |- fprop(a) <=> (a === z)) by RightIff(forward, backward)
    thenHave(fprop(z) |- forall(a, fprop(a) <=> (a === z))) by RightForall
    thenHave(fprop(z) |- exists(z, forall(a, fprop(a) <=> (a === z)))) by RightExists(z)
    thenHave(exists(z, fprop(z)) |- exists(z, forall(a, fprop(a) <=> (a === z)))) by LeftExists
    thenHave(exists(z, fprop(z)) |- existsOne(z, fprop(z))) by RightExistsOne
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Shorthand definitions
   */

  /**
   * Proper Subset --- `x ⊂ y`. Shorthand for `x ⊆ y ∧ x != y`.
   *
   * @param x set
   * @param y set
   */
  def properSubset(x: Term, y: Term) = subset(x, y) /\ !(x === y)

  /**
   * Singleton Set --- `{x}`. Shorthand for `{x, x}`.
   *
   * @param x set
   */
  def singleton(x: Term) = unorderedPair(x, x)

  /**
   * Ordered Pair --- `(x, y)`. Shorthand for `{{x}, {x, y}}`.
   *
   * @param x set
   * @param y set
   */
  def pair(x: Term, y: Term) = unorderedPair(unorderedPair(x, y), singleton(x))

  /**
   * Binary Set Union --- `x ∪ y = ∪ {x, y}`
   *
   * @param x set
   * @param y set
   */
  val setUnion = DEF(x, y) --> union(unorderedPair(x, y))

  /**
   * Successor Function --- Maps a set to its 'successor' in the sense required
   * for an inductive set.
   *
   * `successor: x ↦ x ∪ {x}`
   *
   * @param x set
   */
  val successor = DEF(x) --> union(unorderedPair(x, singleton(x)))

  /**
   * Inductive set --- A set is inductive if it contains the empty set, and the
   * [[successor]]s of each of its elements.
   *
   * `inductive(x) ⇔ (∅ ∈ x ⋀ ∀ y. y ∈ x ⇒ successor(y) ∈ x)`
   *
   * @param x set
   */
  val inductive = DEF(x) --> in(emptySet(), x) /\ forall(y, in(y, x) ==> in(successor(y), x))

  /**
   * Theorem --- There exists an inductive set.
   *
   * Equivalent to the Axiom of Infinity ([[infinityAxiom]]). The proof shows
   * that the two forms are equivalent by folding the definitions of
   * [[successor]] and [[inductive]].
   */
  val inductiveSetExists = makeTHM(
    () |- exists(x, inductive(x))
  ) {
    val form = formulaVariable

    have(() |- forall(x, (x === successor(y)) <=> (x === union(unorderedPair(y, unorderedPair(y, y)))))) by InstFunSchema(Map(x -> y))(successor.definition)
    thenHave(() |- ((successor(y) === successor(y)) <=> (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))))) by InstantiateForall(successor(y))
    val succDef = thenHave(() |- (successor(y) === union(unorderedPair(y, unorderedPair(y, y))))) by Rewrite
    val inductDef = have(() |- inductive(x) <=> in(emptySet(), x) /\ forall(y, in(y, x) ==> in(successor(y), x))) by Rewrite(inductive.definition)

    have(() |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Restate
    val succEq = thenHave(
      (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(successor(y), x))
    ) by RightSubstEq(
      List((successor(y), union(unorderedPair(y, unorderedPair(y, y))))),
      lambda(z, (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(z, x)))
    )
    val iffinst = have(() |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(successor(y), x))) by Cut(succDef, succEq)

    val iffquant = {
      have((in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (in(y, x) ==> in(successor(y), x))) by Weakening(iffinst)
      thenHave(forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (in(y, x) ==> in(successor(y), x))) by LeftForall(y)
      thenHave(forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- forall(y, in(y, x) ==> in(successor(y), x))) by RightForall
      val lhs = thenHave(() |- forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) ==> forall(y, in(y, x) ==> in(successor(y), x))) by Rewrite

      have((in(y, x) ==> in(successor(y), x)) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Weakening(iffinst)
      thenHave(forall(y, in(y, x) ==> in(successor(y), x)) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by LeftForall(y)
      thenHave(forall(y, in(y, x) ==> in(successor(y), x)) |- forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by RightForall
      val rhs = thenHave(() |- forall(y, in(y, x) ==> in(successor(y), x)) ==> forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Rewrite

      have(() |- forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> forall(y, in(y, x) ==> in(successor(y), x))) by RightIff(lhs, rhs)
    }

    have(
      in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- in(emptySet(), x) /\ forall(
        y,
        in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)
      )
    ) by Hypothesis
    thenHave(
      Set(
        forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> forall(y, in(y, x) ==> in(successor(y), x)),
        in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
      ) |- in(emptySet(), x) /\ forall(y, in(y, x) ==> in(successor(y), x))
    ) by RightSubstIff(
      List((forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)), forall(y, in(y, x) ==> in(successor(y), x)))),
      lambda(form, in(emptySet(), x) /\ form)
    )
    val substituted = thenHave(
      Set(
        inductive(x) <=> in(emptySet(), x) /\ forall(y, in(y, x) ==> in(successor(y), x)),
        forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> forall(y, in(y, x) ==> in(successor(y), x)),
        in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
      ) |- inductive(x)
    ) by RightSubstIff(List((inductive(x), in(emptySet(), x) /\ forall(y, in(y, x) ==> in(successor(y), x)))), lambda(form, form))
    val cut1 = have(
      Set(
        forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> forall(y, in(y, x) ==> in(successor(y), x)),
        in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
      ) |- inductive(x)
    ) by Cut(inductDef, substituted)
    val cut2 = have(Set(in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) |- inductive(x)) by Cut(iffquant, cut1)

    thenHave(Set(in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) |- exists(x, inductive(x))) by RightExists(x)
    val rhs = thenHave(Set(exists(x, in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)))) |- exists(x, inductive(x))) by LeftExists

    have(() |- exists(x, inductive(x))) by Cut(infinityAxiom, rhs)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Properties about the empty set and power sets
   */

  /**
   * Theorem --- If a set has an element, then it is not the empty set.
   */
  val setWithElementNonEmpty = makeTHM(
    in(y, x) |- !(x === emptySet())
  ) {
    have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    thenHave(in(y, emptySet()) |- ()) by Rewrite
    thenHave(Set(in(y, x), (x === emptySet())) |- ()) by LeftSubstEq(List((x, emptySet())), lambda(Seq(x), in(y, x)))
    thenHave(in(y, x) |- !(x === emptySet())) by Rewrite
  }

  /**
   * Theorem --- A set containing no elements is equivalent to the empty set.
   */
  val setWithNoElementsIsEmpty = makeTHM(
    forall(y, !in(y, x)) |- (x === emptySet())
  ) {
    have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    thenHave(() |- Set(!in(y, emptySet()), in(y, x))) by Weakening
    val lhs = thenHave(() |- in(y, emptySet()) ==> in(y, x)) by Restate

    have(!in(y, x) |- !in(y, x)) by Hypothesis
    thenHave(!in(y, x) |- Set(!in(y, x), in(y, emptySet()))) by Weakening
    val rhs = thenHave(!in(y, x) |- in(y, x) ==> in(y, emptySet())) by Restate

    have(!in(y, x) |- in(y, x) <=> in(y, emptySet())) by RightIff(lhs, rhs)
    thenHave(forall(y, !in(y, x)) |- in(y, x) <=> in(y, emptySet())) by LeftForall(y)
    val exLhs = thenHave(forall(y, !in(y, x)) |- forall(y, in(y, x) <=> in(y, emptySet()))) by RightForall

    have(() |- forall(z, in(z, x) <=> in(z, emptySet())) <=> (x === emptySet())) by InstFunSchema(Map(x -> x, y -> emptySet()))(extensionalityAxiom)
    val exRhs = thenHave(() |- forall(y, in(y, x) <=> in(y, emptySet())) <=> (x === emptySet())) by Restate

    have(forall(y, !in(y, x)) |- (forall(y, in(y, x) <=> in(y, emptySet())) <=> (x === emptySet())) /\ forall(y, in(y, x) <=> in(y, emptySet()))) by RightAnd(exLhs, exRhs)
    thenHave(forall(y, !in(y, x)) |- (x === emptySet())) by Trivial
  }

  /**
   * Theorem --- The empty set is a subset of every set.
   */
  val emptySetIsASubset = makeTHM(
    () |- subset(emptySet(), x)
  ) {
    val lhs = have(() |- subset(emptySet(), x) <=> forall(z, in(z, emptySet()) ==> in(z, x))) by InstFunSchema(Map(x -> emptySet(), y -> x))(subsetAxiom)

    have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    thenHave(() |- in(y, emptySet()) ==> in(y, x)) by Weakening
    val rhs = thenHave(() |- forall(y, in(y, emptySet()) ==> in(y, x))) by RightForall

    have(() |- (subset(emptySet(), x) <=> forall(z, in(z, emptySet()) ==> in(z, x))) /\ forall(y, in(y, emptySet()) ==> in(y, x))) by RightAnd(lhs, rhs)
    thenHave(() |- (subset(emptySet(), x) <=> forall(z, in(z, emptySet()) ==> in(z, x))) /\ forall(z, in(z, emptySet()) ==> in(z, x))) by Restate
    thenHave(() |- subset(emptySet(), x)) by Trivial
  }

  /**
   * Theorem --- A power set is never empty.
   */
  val powerSetNonEmpty = makeTHM(
    () |- !(powerSet(x) === emptySet())
  ) {
    // strategy
    //      prove power set contains empty set
    //      since it has an element, it is not empty itself

    val lhs = have(() |- in(emptySet(), powerSet(x)) <=> subset(emptySet(), x)) by InstFunSchema(Map(x -> emptySet(), y -> x))(powerAxiom)

    have(() |- (in(emptySet(), powerSet(x)) <=> subset(emptySet(), x)) /\ subset(emptySet(), x)) by RightAnd(lhs, emptySetIsASubset)
    val emptyinPower = thenHave(() |- in(emptySet(), powerSet(x))) by Trivial
    val nonEmpty = have(in(emptySet(), powerSet(x)) |- !(powerSet(x) === emptySet())) by InstFunSchema(Map(y -> emptySet(), x -> powerSet(x)))(setWithElementNonEmpty)

    have(() |- !(powerSet(x) === emptySet())) by Cut(emptyinPower, nonEmpty)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Properties about pairs
   */

  /**
   * Theorem --- First Element in Pair
   *
   *    `x ∈ {x, y}`
   *
   * Unfolds the definition of [[unorderedPair]]. Easier to use in theorems than
   * the complete definition.
   */
  val firstElemInPair = makeTHM(
    () |- in(x, unorderedPair(x, y))
  ) {
    val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstFunSchema(Map(x -> x, y -> y, z -> z))(ax"pairAxiom")
    have((z === x) |- (z === x)) by Hypothesis
    val rhs = thenHave((z === x) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === x) |- (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    thenHave((z === x) |- in(z, unorderedPair(x, y))) by Trivial
    thenHave((x === x) |- in(x, unorderedPair(x, y))) by InstFunSchema(Map(z -> x))
    thenHave(() |- in(x, unorderedPair(x, y))) by LeftRefl
  }

  /**
   * Theorem --- Second Element in Pair
   *
   *    `y ∈ {x, y}`
   *
   * Unfolds the definition of [[unorderedPair]]. Easier to use in theorems than
   * the complete definition.
   */
  val secondElemInPair = makeTHM(
    () |- in(y, unorderedPair(x, y))
  ) {
    val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstFunSchema(Map(x -> x, y -> y, z -> z))(ax"pairAxiom")
    have((z === y) |- (z === y)) by Hypothesis
    val rhs = thenHave((z === y) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === y) |- (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    thenHave((z === y) |- in(z, unorderedPair(x, y))) by Trivial
    thenHave((y === y) |- in(y, unorderedPair(x, y))) by InstFunSchema(Map(z -> y))
    thenHave(() |- in(y, unorderedPair(x, y))) by LeftRefl
  }

  /**
   * Theorem --- If a set belongs to a singleton, it must be the single element.
   */
  val singletonHasNoExtraElements = makeTHM(
    () |- in(y, singleton(x)) <=> (x === y)
  ) {
    // specialization of the pair axiom to a singleton

    have(() |- in(y, unorderedPair(x, x)) <=> (x === y) \/ (x === y)) by InstFunSchema(Map(x -> x, y -> x, z -> y))(pairAxiom)
    thenHave(() |- in(y, singleton(x)) <=> (x === y)) by Restate
  }

  val unorderedPairSymmetry = makeTHM(() |- unorderedPair(x, y) === unorderedPair(y, x)) {
    have(() |- (y === z) \/ (x === z) <=> in(z, unorderedPair(y, x))) by InstFunSchema(Map(x -> y, y -> x))(pairAxiom)
    andThen(applySubst.apply(pairAxiom))
    val part1 = thenHave(() |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))) by RightForall
    val part2 = have(() |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x))) by InstFunSchema(
      Map(x -> unorderedPair(x, y), y -> unorderedPair(y, x))
    )(extensionalityAxiom)
    val fin = have(applySubst(forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x)))(part1))
    have(thesis) by Cut(part2, fin)
  }

  val unorderedPairDeconstruction = makeTHM("unorderedPair('a, 'b) = unorderedPair('c, 'd) ⊢ 'a = 'c ∧ 'b = 'd ∨ 'a = 'd ∧ 'b = 'c") {
    val s1 = have(applySubst("unorderedPair('a, 'b) = unorderedPair('c, 'd)")(pairAxiom of (x -> a, y -> b)))
    val base = have(applySubst(s1)(pairAxiom of (x -> c, y -> d)))
    have(thesis) by Tautology.from(base of (z -> a), base of (z -> b), base of (z -> c), base of (z -> d))
  }

  /**
   * Theorem --- Union of a Singleton is the Original Set
   *
   * The unary [[union]] operation unfolds a [[singleton]] into the single
   * element
   *
   *      `∀ x. ∪ {x} === x`
   */
  val unionOfSingletonIsTheOriginalSet = makeTHM(
    () |- (union(singleton(x)) === x)
  ) {
    val X = singleton(x)

    // need to prove:
    //    ∀ z. z ∈ ∪ X <=> z ∈ x

    // forward direction
    //  z ∈ x |- z ∈ ∪ X
    val unionAx = have(() |- in(z, union(X)) <=> exists(y, in(z, y) /\ in(y, X))) by InstFunSchema(Map(x -> z, z -> X))(unionAxiom)
    thenHave(in(z, union(X)) |- exists(y, in(z, y) /\ in(y, X))) by Trivial

    val andLhs = have(() |- in(x, X)) by InstFunSchema(Map(y -> x))(firstElemInPair)
    val andRhs = have(in(z, x) |- in(z, x)) by Hypothesis
    have(in(z, x) |- in(z, x) /\ in(x, X)) by RightAnd(andLhs, andRhs)
    val fwdLhs = thenHave(in(z, x) |- exists(y, in(z, y) /\ in(y, X))) by RightExists(x)
    have(in(z, x) |- exists(y, in(z, y) /\ in(y, X)) /\ (in(z, union(X)) <=> exists(y, in(z, y) /\ in(y, X)))) by RightAnd(fwdLhs, unionAx)
    thenHave(in(z, x) |- in(z, union(X))) by Trivial
    val fwd = thenHave(() |- in(z, x) ==> in(z, union(X))) by Rewrite

    // backward direction
    //  z ∈ ∪ X |- z ∈ x

    have(in(y, X) |- in(y, X)) by Hypothesis
    val bwdHypo = thenHave(in(z, y) /\ in(y, X) |- in(y, X)) by Weakening
    have(in(z, y) /\ in(y, X) |- in(y, X) /\ (in(y, X) <=> (x === y))) by RightAnd(bwdHypo, singletonHasNoExtraElements)
    val cutLhs = thenHave(in(z, y) /\ in(y, X) |- (x === y)) by Trivial

    have(in(z, y) |- in(z, y)) by Hypothesis
    thenHave(in(y, X) /\ in(z, y) |- in(z, y)) by Weakening
    val cutRhs = thenHave(Set(in(z, y) /\ in(y, X), (x === y)) |- in(z, x)) by RightSubstEq(List((y, x)), lambda(y, in(z, y)))

    have(in(z, y) /\ in(y, X) |- in(z, x)) by Cut(cutLhs, cutRhs)
    val bwdRhs = thenHave(exists(y, in(z, y) /\ in(y, X)) |- in(z, x)) by LeftExists
    val bwdLhs = have(in(z, union(X)) |- exists(y, in(z, y) /\ in(y, X))) by Weakening(unionAx)
    have(in(z, union(X)) |- in(z, x)) by Cut(bwdLhs, bwdRhs)
    val bwd = thenHave(() |- in(z, union(X)) ==> in(z, x)) by Rewrite

    have(() |- in(z, union(X)) <=> in(z, x)) by RightIff(fwd, bwd)
    val iff = thenHave(() |- forall(z, in(z, union(X)) <=> in(z, x))) by RightForall
    val extAx = have(() |- forall(z, in(z, union(X)) <=> in(z, x)) <=> (union(X) === x)) by InstFunSchema(Map(x -> union(X), y -> x))(extensionalityAxiom)

    have(() |- forall(z, in(z, union(X)) <=> in(z, x)) /\ (forall(z, in(z, union(X)) <=> in(z, x)) <=> (union(X) === x))) by RightAnd(iff, extAx)
    thenHave(() |- (union(X) === x)) by Trivial
  }

  /**
   * Theorem --- Two unordered pairs are equal iff their elements are equal pairwise.
   */
  val unorderedPairExtensionality = makeTHM(
    () |- (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))
  ) {
    // forward direction
    //      up ab = up cd |- a = c and b = d OR a = d and b = c
    val fwd = have(() |- (unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by Rewrite(unorderedPairDeconstruction)

    // backward direction
    //      a = c and b = d => up ab = up cd (and the other case)
    have(() |- unorderedPair(a, b) === unorderedPair(a, b)) by RightRefl
    thenHave(Set(a === c, b === d) |- unorderedPair(a, b) === unorderedPair(c, d)) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(x, y)))
    val lhs = thenHave(Set((a === c) /\ (b === d)) |- unorderedPair(a, b) === unorderedPair(c, d)) by Rewrite

    have(() |- unorderedPair(a, b) === unorderedPair(b, a)) by InstFunSchema(Map(x -> a, y -> b))(unorderedPairSymmetry)
    thenHave(Set(a === d, b === c) |- (unorderedPair(a, b) === unorderedPair(c, d))) by RightSubstEq(List((a, d), (b, c)), lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(y, x)))
    val rhs = thenHave(Set((a === d) /\ (b === c)) |- (unorderedPair(a, b) === unorderedPair(c, d))) by Rewrite

    have((((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) |- (unorderedPair(a, b) === unorderedPair(c, d))) by LeftOr(lhs, rhs)
    val bwd = thenHave(() |- (((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) ==> (unorderedPair(a, b) === unorderedPair(c, d))) by Rewrite

    have(() |- (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by RightIff(fwd, bwd)
  }

  /**
   * Theorem --- A singleton set is never empty.
   */
  val singletonNonEmpty = makeTHM(
    () |- !(singleton(x) === emptySet())
  ) {
    val reflLhs = have(() |- in(x, singleton(x)) <=> (x === x)) by InstFunSchema(Map(y -> x))(singletonHasNoExtraElements)

    val reflRhs = have(() |- (x === x)) by RightRefl
    have(() |- (x === x) /\ (in(x, singleton(x)) <=> (x === x))) by RightAnd(reflLhs, reflRhs)
    val lhs = thenHave(() |- in(x, singleton(x))) by Trivial

    val rhs = have(in(x, singleton(x)) |- !(singleton(x) === emptySet())) by InstFunSchema(Map(y -> x, x -> singleton(x)))(setWithElementNonEmpty)

    have(() |- !(singleton(x) === emptySet())) by Cut(lhs, rhs)
  }

  /**
   * Theorem --- Two singletons are equal iff their elements are equal
   */
  val singletonExtensionality = makeTHM(
    () |- (singleton(x) === singleton(y)) <=> (x === y)
  ) {
    // forward direction
    // {x} === {y} |- x === y
    have(() |- forall(z, in(z, singleton(x)) <=> in(z, singleton(y))) <=> (singleton(x) === singleton(y))) by InstFunSchema(Map(x -> singleton(x), y -> singleton(y)))(extensionalityAxiom)
    thenHave((singleton(x) === singleton(y)) |- forall(z, in(z, singleton(x)) <=> in(z, singleton(y)))) by Trivial
    val singiff = thenHave((singleton(x) === singleton(y)) |- in(z, singleton(x)) <=> in(z, singleton(y))) by InstantiateForall(z)

    val singX = have(() |- in(z, singleton(x)) <=> (z === x)) by InstFunSchema(Map(y -> z))(singletonHasNoExtraElements)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(x)) <=> in(z, singleton(y))) /\ (in(z, singleton(x)) <=> (z === x))) by RightAnd(singiff, singX)
    val yToX = thenHave((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x))) by Trivial

    val singY = have(() |- in(z, singleton(y)) <=> (z === y)) by InstFunSchema(Map(x -> y))(singX)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x)) /\ (in(z, singleton(y)) <=> (z === y))) by RightAnd(yToX, singY)
    thenHave((singleton(x) === singleton(y)) |- ((z === x) <=> (z === y))) by Trivial
    thenHave((singleton(x) === singleton(y)) |- ((x === x) <=> (x === y))) by InstFunSchema(Map(z -> x))

    thenHave((singleton(x) === singleton(y)) |- (x === y)) by Rewrite
    val fwd = thenHave(() |- (singleton(x) === singleton(y)) ==> (x === y)) by Trivial

    // backward direction
    //  x === y |- {x} === {y}
    have(() |- singleton(x) === singleton(x)) by RightRefl
    thenHave((x === y) |- singleton(x) === singleton(y)) by RightSubstEq(List((x, y)), lambda(a, singleton(x) === singleton(a)))
    val bwd = thenHave(() |- (x === y) ==> (singleton(x) === singleton(y))) by Rewrite

    have(() |- (singleton(x) === singleton(y)) <=> (x === y)) by RightIff(fwd, bwd)
  }

  /**
   * Two ordered pairs are equal iff their elements are equal when taken in order.
   *
   *  pair(a, b) === {{a}, {a, b}}
   *
   *  pair(a, b) === pair(c, d) iff a === c and b === d
   */
  // val pairExtensionality = makeTHM(
  //     () |- (pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))
  // ) {
  //     // forward direction
  //     //  (a === c) /\ (b === d) |- pair a b === pair c d

  //     have(() |- (pair(a, b) === pair(a, b))) by RightRefl
  //     thenHave(Set((a === c), (b === d)) |- (pair(a, b) === pair(c, d))) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(x, y), pair(a, b) === pair(x, y)))
  //     val fwd = thenHave(() |- ((a === c) /\ (b === d)) ==> (pair(a, b) === pair(c, d))) by Rewrite

  //     // backward direction
  //     //  pair a b === pair c d |- (a === c) /\ (b === d)

  //     val oPairAxAB = have(() |- in(z, pair(a, b)) <=> ((unorderedPair(a, b) === z) \/ (singleton(a) === z))) by InstFunSchema(Map(y -> singleton(a), x -> unorderedPair(a, b)))(pairAxiom)
  //     val oPairAxCD = have(() |- in(z, pair(c, d)) <=> ((unorderedPair(c, d) === z) \/ (singleton(c) === z))) by InstFunSchema(Map(a -> c, b -> d))(oPairAxAB)

  //     have(() |- forall(z, in(z, pair(a, b)) <=> in(z, pair(c, d))) <=> (pair(a, b) === pair(c, d))) by InstFunSchema(Map(x -> pair(a, b), y -> pair(c, d)))(extensionalityAxiom)
  //     thenHave((pair(a, b) === pair(c, d)) |- forall(z, in(z, pair(a, b)) <=> in(z, pair(c, d)))) by Trivial
  //     val eqIff = thenHave((pair(a, b) === pair(c, d)) |- in(z, pair(a, b)) <=> in(z, pair(c, d))) by InstantiateForall(z)

  //     have((pair(a, b) === pair(c, d)) |- (in(z, pair(a, b)) <=> in(z, pair(c, d))) /\ (in(z, pair(a, b)) <=> ((singleton(a) === z) \/ (unorderedPair(a, b) === z)))) by RightAnd(oPairAxAB, eqIff)
  //     val cdToab = thenHave((pair(a, b) === pair(c, d)) |- (in(z, pair(c, d)) <=> ((singleton(a) === z) \/ (unorderedPair(a, b) === z)))) by Trivial

  //     have((pair(a, b) === pair(c, d)) |- (in(z, pair(c, d)) <=> ((singleton(a) === z) \/ (unorderedPair(a, b) === z))) /\ (in(z, pair(c, d)) <=> ((singleton(c) === z) \/ (unorderedPair(c, d) === z)))) by RightAnd(cdToab, oPairAxCD)
  //     val stmtz = thenHave((pair(a, b) === pair(c, d)) |- (((singleton(a) === z) \/ (unorderedPair(a, b) === z)) <=> ((singleton(c) === z) \/ (unorderedPair(c, d) === z)))) by Trivial

  //     // unordered pair extensionality
  //     val upExt = have(() |- (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((b === c) /\ (a === d)))) by Rewrite(unorderedPairExtensionality)
  //     // we will instantiate this to eliminate assumptions for our cases

  //     def upEq(a: Term, b: Term, c: Term, d: Term) = unorderedPair(a, b) === unorderedPair(c, d)
  //     def termEq(a: Term, b: Term, c: Term, d: Term) = (a === c) /\ (b === d)
  //     def upEqIff(a: Term, b: Term, c: Term, d: Term) = upEq(a, b, c, d) <=> termEq(a, b, c, d)

  //     val q = formulaVariable
  //     val w = formulaVariable
  //     val e = formulaVariable
  //     val r = formulaVariable

  //     // a != c
  //     val assumption = (upEq(a, a, a, a) \/ upEq(a, b, a, a)) <=> (upEq(c, c, a, a) \/ upEq(c, d, a, a))
  //     val assumption2 = (upEq(a, a, a, b) \/ upEq(a, b, a, b)) <=> (upEq(c, c, a, b) \/ upEq(c, d, a, b))
  //     val decomposition = Set(upEqIff(a, a, a, a), upEqIff(a, b, a, a), upEqIff(c, c, a, a), upEqIff(c, d, a, a))
  //     val decomposition2 = Set(upEqIff(a, a, a, b), upEqIff(a, b, a, b), upEqIff(c, c, a, b), upEqIff(c, d, a, b))

  //     // case z = {a}
  //     // derive a = c
  //     have((pair(a, b) === pair(c, d)) |- assumption) by InstFunSchema(Map(z -> singleton(a)))(stmtz)
  //     thenHave((decomposition + (pair(a, b) === pair(c, d))) |- assumption) by Weakening
  //     thenHave((decomposition + (pair(a, b) === pair(c, d))) |- ((termEq(a, a, a, a) \/ termEq(a, b, a, a)) <=> (termEq(c, c, a, a) \/ termEq(c, d, a, a)))) by RightSubstIff(List((upEq(a, a, a, a), termEq(a, a, a, a)), (upEq(a, b, a, a), termEq(a, b, a, a)), (upEq(c, c, a, a), termEq(c, c, a, a)), (upEq(c, d, a, a), termEq(c, d, a, a))), lambda(Seq(q, w, e, r), (q \/ w) <=> (e \/ r)))
  //     val aEqc = thenHave((decomposition + (pair(a, b) === pair(c, d))) |- (a === c)) by Rewrite

  //     // then get two cases, in both cases derive the conclusion
  //     have((pair(a, b) === pair(c, d)) |- assumption2) by InstFunSchema(Map(z -> unorderedPair(a, b)))(stmtz)
  //     thenHave((decomposition2 + (pair(a, b) === pair(c, d)) + (a === c)) |- assumption2) by Weakening
  //     thenHave((decomposition2 + (pair(a, b) === pair(c, d)) + (a === c)) |- ((termEq(a, a, a, b) \/ termEq(a, b, a, b)) <=> (termEq(c, c, a, b) \/ termEq(c, d, a, b)))) by RightSubstIff(List((upEq(a, a, a, b), termEq(a, a, a, b)), (upEq(a, b, a, b), termEq(a, b, a, b)), (upEq(c, c, a, b), termEq(c, c, a, b)), (upEq(c, d, a, b), termEq(c, d, a, b))), lambda(Seq(q, w, e, r), (q \/ w) <=> (e \/ r)))
  //     val caseSplit = thenHave((decomposition2 + (pair(a, b) === pair(c, d)) + (a === c)) |- (termEq(c, c, a, b) \/ termEq(c, d, a, b))) by Rewrite

  //     // TODO: finish this proof
  //     // probably by z = {c, d} and then get the other symmetric condition, reduce them together
  //     // too much pain

  // }

  /**
   * Theorem --- No set is an element of itself.
   *
   * This is imposed by the Foundation Axiom ([[foundationAxiom]]).
   */
  val selfNonInclusion = makeTHM(
    () |- !in(x, x)
  ) {
    val X = singleton(x)

    have(() |- !(X === emptySet()) ==> exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))) by InstFunSchema(Map(x -> X))(foundationAxiom)
    val lhs = thenHave(!(X === emptySet()) |- exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))) by Restate

    have(in(y, X) |- in(y, X) <=> (x === y)) by Weakening(singletonHasNoExtraElements)
    val innerRhs = thenHave(in(y, X) |- (x === y)) by Trivial

    have(Set(in(x, X), (in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by Hypothesis
    thenHave(Set(in(x, X), forall(z, in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by LeftForall(z)
    thenHave(Set(in(x, X), forall(z, in(z, X) ==> !in(z, x)), in(x, X)) |- in(x, X) ==> !in(x, x)) by InstFunSchema(Map(z -> x, y -> x))
    val coreRhs = thenHave(in(x, X) /\ forall(z, in(z, X) ==> !in(z, x)) |- !in(x, x)) by Restate

    // now we need to show that the assumption is indeed true
    // this requires destruction of the existential quantifier in lhs
    have(in(x, X) /\ forall(z, in(z, X) ==> !in(z, x)) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Hypothesis
    val innerRhs2 = thenHave(Set(in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)), x === y) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by LeftSubstEq(
      List((x, y)),
      lambda(Seq(y), in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))
    )

    have(Set(in(y, X), in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Cut(innerRhs, innerRhs2)
    thenHave(in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Restate
    val coreLhs = thenHave(exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by LeftExists

    val rhs = have(exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- !in(x, x)) by Cut(coreLhs, coreRhs)

    val finRhs = have(!(X === emptySet()) |- !in(x, x)) by Cut(lhs, rhs)
    val finLhs = have(() |- !(X === emptySet())) by Rewrite(singletonNonEmpty)

    have(() |- !in(x, x)) by Cut(finLhs, finRhs)
  }

  /**
   * Theorem --- No Universal Set
   *
   * There does not exist a set of all sets. Alternatively, its existence, with
   * the comprehension schema and Russel's paradox, produces a contradiction.
   */
  val noUniversalSet = makeTHM(
    forall(z, in(z, x)) |- ()
  ) {
    have(in(x, x) |- ()) by Rewrite(selfNonInclusion)
    thenHave(forall(z, in(z, x)) |- ()) by LeftForall(x)
  }

  /**
   * Theorem --- The power set of any set is not a proper subset of it.
   */
  val powerSetNonInclusion = makeTHM(
    Exists(x, properSubset(powerSet(x), x)) |- ()
  ) {
    val lhs = have(subset(powerSet(x), x) |- subset(powerSet(x), x)) by Hypothesis

    val rhs = have(() |- in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x)) by InstFunSchema(Map(x -> powerSet(x), y -> x))(powerAxiom)

    have(subset(powerSet(x), x) |- subset(powerSet(x), x) /\ (in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x))) by RightAnd(lhs, rhs)
    val contraLhs = thenHave(subset(powerSet(x), x) |- in(powerSet(x), powerSet(x))) by Trivial

    val contraRhs = have(() |- !in(powerSet(x), powerSet(x))) by InstFunSchema(Map(x -> powerSet(x)))(selfNonInclusion)

    have(subset(powerSet(x), x) |- !in(powerSet(x), powerSet(x)) /\ in(powerSet(x), powerSet(x))) by RightAnd(contraLhs, contraRhs)
    thenHave(subset(powerSet(x), x) |- ()) by Restate
    thenHave(subset(powerSet(x), x) |- (x === powerSet(x))) by Weakening
    thenHave(properSubset(powerSet(x), x) |- ()) by Restate
    thenHave(exists(x, properSubset(powerSet(x), x)) |- ()) by LeftExists
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Operations on Sets
   */

  val setIntersectionUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ in(t, y))))
  ) {
    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ in(t, y))))) by UniqueComprehension(x, lambda(Seq(t, z), in(t, y)))
  }

  /**
   * Binary Set Intersection --- Intersection of two sets.
   *
   *     `x ∩ y = {z ∈ x | z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val setIntersection = DEF(x, y) --> The(z, forall(t, in(t, z) <=> (in(t, x) /\ in(t, y))))(setIntersectionUniqueness)

  val unaryIntersectionUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))
  ) {
    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))) by UniqueComprehension(union(x), lambda(Seq(t, z), forall(b, in(b, x) ==> in(t, b))))
  }

  /**
   * Unary Set Intersection --- Intersection of all elements of a given set.
   *
   *     `∩ x = {z ∈ ∪ x | ∀ y ∈ x. z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param x set
   */
  val unaryIntersection = DEF(x) --> The(z, forall(t, in(t, z) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))(unaryIntersectionUniqueness)

  val setDifferenceUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))
  ) {
    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))) by UniqueComprehension(x, lambda(Seq(t, z), !in(t, y)))
  }

  /**
   * Binary Set Difference --- Given two sets, produces the set that contains
   * elements in the first but not in the second. `x - y = {z ∈ x | ! z ∈
   * y}` The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val setDifference = DEF(x, y) --> The(z, forall(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))(setDifferenceUniqueness)

  /**
   * Theorem --- Intersection of a non-empty Class is a Set
   *
   * There exists a set that is the intersection of all sets satisfying a given
   * formula. With classes, this means that the unary intersection of a class
   * defined by a predicate is a set.
   *
   *    `∃ x. P(x) ⊢ ∃ z. t ∈ z ⇔ ∀ x. P(x) ⇒ t ∈ x`
   */
  val intersectionOfPredicateClassExists = makeTHM(
    exists(x, P(x)) |- exists(z, forall(t, in(t, z) <=> forall(y, P(y) ==> in(t, y))))
  ) {
    have(() |- exists(z, forall(t, in(t, z) <=> (in(t, x) /\ sPhi(t, x))))) by InstFunSchema(Map(z -> x))(comprehensionSchema)

    val conjunction = thenHave(() |- exists(z, forall(t, in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, x), forall(y, P(y) ==> in(t, y)))))

    have(forall(y, P(y) ==> in(t, y)) |- forall(y, P(y) ==> in(t, y))) by Hypothesis
    thenHave(forall(y, P(y) ==> in(t, y)) /\ P(x) |- forall(y, P(y) ==> in(t, y))) by Weakening
    thenHave(forall(y, P(y) ==> in(t, y)) /\ P(x) |- P(x) ==> in(t, x)) by InstantiateForall(x)
    thenHave(forall(y, P(y) ==> in(t, y)) /\ P(x) |- in(t, x) /\ forall(y, P(y) ==> in(t, y))) by Trivial
    val fwd = thenHave(P(x) |- forall(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Rewrite

    have((in(t, x) /\ forall(y, P(y) ==> in(t, y))) |- (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Hypothesis
    val bwd = thenHave(() |- (in(t, x) /\ forall(y, P(y) ==> in(t, y))) ==> (forall(y, P(y) ==> in(t, y)))) by Rewrite

    val lhs = have(P(x) |- forall(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by RightIff(fwd, bwd)

    val form = formulaVariable
    have((in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) |- in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Hypothesis
    val rhs = thenHave(
      Set((in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))), (forall(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))) |- (in(t, z) <=> (forall(y, P(y) ==> in(t, y))))
    ) by RightSubstIff(List((forall(y, P(y) ==> in(t, y)), (in(t, x) /\ forall(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))

    have(Set(P(x), (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))) |- in(t, z) <=> (forall(y, P(y) ==> in(t, y)))) by Cut(lhs, rhs)
    thenHave(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- in(t, z) <=> (forall(y, P(y) ==> in(t, y)))) by LeftForall(t)
    thenHave(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y))))) by RightForall
    thenHave(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by RightExists(z)
    val cutRhs = thenHave(Set(P(x), exists(z, forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))))) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by LeftExists

    have(P(x) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by Cut(conjunction, cutRhs)
    thenHave(exists(x, P(x)) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by LeftExists

  }

  /**
   * The first element of an ordered [[pair]] --- `first p = \cup \cap p`
   *
   * If `p = (a, b) = {{a}, {a, b}}`, `\cap p = {a}`, and `\cup \cap p = a`.
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage.
   */
  val firstInPair = DEF (p) --> union(unaryIntersection(p))


  val secondInPairSingletonUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))
  ) {
    have(thesis) by UniqueComprehension(union(p), lambda(Seq(t, x), ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p))))))
  }

  /**
    * See [[secondInPair]].
    */
  val secondInPairSingleton = DEF (p) --> The(z, forall(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))(secondInPairSingletonUniqueness)

  /**
   * The second element of an ordered [[pair]] --- `second p = \cup {x \in \cup
   * p | \cup p != \cap p ==> !x \in \cap p} = \cup ([[secondInPairSingleton]]
   * p)`
   *
   * There is a more naive definition: `second p = \cup (\cup p \ (first p))`.
   * If `p = (a, b) = {{a}, {a, b}}`, `\cup p = {a, b}`, and `\cup p \ (first p)
   * = {a, b} \ {a} = {b}`, the `\cup` at the top level reduces this to `b`.
   * However, this fails when `a = b`, and returns the [[emptySet]].
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage.
   *
   * @see https://en.wikipedia.org/wiki/Ordered_pair#Kuratowski's_definition
   */
  val secondInPair = DEF (p) --> union(secondInPairSingleton(p))

  /**
   * Cartesian Products and Relations
   */

  val cartesianProductUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, powerSet(setUnion(x, y))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))
  ) {
    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, powerSet(setUnion(x, y))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))) by UniqueComprehension(
      powerSet(setUnion(x, y)),
      lambda(Seq(t, z), exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))
    )
  }

  /**
   * Cartesian Product --- Given two sets `x` and `y`, their cartesian product
   * is the set containing pairs with the first element in `x` and the second
   * in `y`. The cartesian product can be seen as a comprehension on the set
   * `PP(x ∪ y)`.
   *
   *     `x * y = {z ∈ PP(x ∪ y) | ∃ a ∈ x, b ∈ y. z = (a, b)}`
   *
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val cartesianProduct =
    DEF(x, y) --> The(z, forall(t, in(t, z) <=> (in(t, powerSet(setUnion(x, y))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))(cartesianProductUniqueness)

  /**
   * Binary Relation --- A binary relation `r` on `x` is a subset of the
   * [[cartesianProduct]] of `x` with itself, `x * x`. We say `a r b`, `r(a,
   * b)`, or `r relates a to b` for `(a, b) ∈ r`.
   */
  val relation = DEF(r, x) --> subset(r, cartesianProduct(x, x))

  val relationDomainUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))
  ) {
    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))) by UniqueComprehension(union(union(r)), lambda(Seq(t, b), exists(a, in(pair(t, a), r))))
  }

  /**
   * (Binary) Relation Domain --- The set containing the first elements of every
   * pair in a relation `r`. Alternatively, the set of elements which are
   * related to another element by `r`.
   *
   *      `dom(r) = {z ∈ ∪ ∪ r | ∃ t. (z, t) ∈ r}`
   *
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param r relation (set)
   */
  val relationDomain = DEF(r) --> The(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))(relationDomainUniqueness)

  val relationRangeUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))
  ) {
    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))) by UniqueComprehension(union(union(r)), lambda(Seq(t, b), exists(a, in(pair(a, t), r))))
  }

  /**
   * (Binary) Relation Range --- The set containing the second elements of every
   * pair in a relation `r`. Alternatively, the set of elements which another
   * element relates to by `r`.
   *
   *      `range(r) = {z ∈ ∪ ∪ r | ∃ t. (t, z) ∈ r}
   *
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param r relation (set)
   */
  val relationRange = DEF(r) --> The(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))(relationRangeUniqueness)

  /**
   * (Binary) Relation Field --- The union of the domain and range of a
   * relation, or the set of all elements related by `r`.
   *
   * @param r relation (set)
   */
  val relationField = DEF(r) --> (setUnion(relationDomain(r), relationRange(r)))

  /**
   * Functional Over a Domain --- A binary relation is functional over a domain
   * if it relates every element `x` in the domain to a unique element `y`.
   *
   *     `functionalOver(f, x) ⇔ relation(f, x) ∧ ∀ z ∈ x. ∃! y. (z, y) ∈ f`
   *
   * We may alternatively denote `(z, y) ∈ f` as `y = f(z)`.
   *
   * @param f relation (set)
   * @param x set
   */
  val functionalOver = DEF(f, x) --> (relation(f, x) /\ forall(z, in(z, x) ==> existsOne(y, in(pair(z, y), f))))

  /**
   * Functional --- A binary relation is functional if it is functional over its own domain.
   *
   * @param f relation (set)
   */
  val functional = DEF(f) --> functionalOver(f, relationDomain(f))

  /**
   * Function application
   */
  // val App = DEF (f, x) --> The(z, functional(f) ==> in(pair(x, z), f))(functionApplicationUniqueness)

  val restrictedFunctionUniqueness = makeTHM(
    () |- existsOne(g, forall(t, in(t, g) <=> (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))
  ) {
    have(() |- existsOne(g, forall(t, in(t, g) <=> (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))) by UniqueComprehension(
      f,
      lambda(Seq(t, b), exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))
    )
  }

  /**
   * Function Restriction ---  The restriction of a function f to a domain x,
   * also written as f_x.
   *
   *    `restrictedFunction(f, x) === {(y, f(y)) | y ∈ x}`
   *
   * @param f function (set)
   * @param x set to restrict to
   */
  val restrictedFunction = DEF(f, x) --> The(g, forall(t, in(t, g) <=> (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))(restrictedFunctionUniqueness)

  // TODO: functional restricted over x has its domain as x ∈tersect dom f

  // TODO: any subset of a functional is functional
  // TODO: a functional over something restricted to x is still functional

  /**
   * Sigma Pi Lambda
   */

  /**
   * Dependent Sum (Sigma)
   *
   * TODO: explain
   */
  val Sigma = DEF(x, f) --> union(restrictedFunction(f, x))

  val piUniqueness = makeTHM(
    () |- existsOne(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))
  ) {
    have(() |- existsOne(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))) by UniqueComprehension(
      powerSet(Sigma(x, f)),
      lambda(Seq(z, y), (subset(x, relationDomain(z)) /\ functional(z)))
    )
  }

  /**
   * Dependent Product (Pi)
   *
   * TODO: explain
   */
  val Pi = DEF(x, f) --> The(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))(piUniqueness)

  /**
   * Properties of relations
   */

  /**
   * Reflexive Relation --- `∀ x. x R x`
   */
  val reflexive = DEF(r, x) --> relation(r, x) /\ forall(y, in(y, x) ==> in(pair(y, y), r))

  /**
   * Symmetric Relation --- `∀ x y. x R y ⇔ y R x`
   */
  val symmetric = DEF(r, x) --> relation(r, x) /\ forall(y, forall(z, in(pair(y, z), r) <=> in(pair(z, y), r)))

  /**
   * Transitive Relation --- `∀ x y z. x R y ∧ y R z ⇒ x R z`
   */
  val transitive = DEF(r, x) --> relation(r, x) /\ forall(w, forall(y, forall(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))))

  /**
   * Equivalence Relation --- A relation is an equivalence relation if it is
   * [[reflexive]], [[symmetric]], and [[transitive]].
   */
  val equivalence = DEF(r, x) --> reflexive(r, x) /\ symmetric(r, x) /\ transitive(r, x)

  /**
   * Anti-reflexive Relation --- `∀ x. ! x R x`
   */
  val antiReflexive = DEF(r, x) --> relation(r, x) /\ forall(y, in(y, x) ==> !in(pair(y, y), r))

  /**
   * Irreflexive Relation --- Alias for [[antiReflexive]].
   */
  val irreflexive = antiReflexive

  /**
   * Anti-symmetric Relation --- `∀ x y. x R y ∧ y R x ⇒ y = x`
   */
  val antiSymmetric = DEF(r, x) --> relation(r, x) /\ forall(y, forall(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))

  /**
   * Asymmetric Relation --- `∀ x y. x R y ⇔ ! y R x`
   */
  val asymmetric = DEF(r, x) --> relation(r, x) /\ forall(y, forall(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))

  /**
   * Connected Relation --- `∀ x y. (x R y) ∨ (y R x) ∨ (y = x)`
   */
  val connected = DEF(r, x) --> relation(r, x) /\ forall(y, forall(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z))))

  /**
   * Total Relation --- Alias for [[connected]].
   */
  val total = connected

  /**
   * Strongly Connected Relation ---
   *     `∀ x y z. y R x ∧ z R x ⇒ y R z ∨ z R y`
   */
  val stronglyConnected = DEF(r, x) --> relation(r, x) /\ forall(y, forall(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r))))

  /**
   * Inductive and transitive sets
   */

  /**
   * Theorem --- There exists an intersection of all inductive sets
   */
  val inductiveIntersectionExistence = makeTHM(
    () |- exists(z, forall(t, in(t, z) <=> forall(y, inductive(y) ==> in(t, y))))
  ) {
    val inductExt =
      have(exists(x, inductive(x)) |- exists(z, forall(t, in(t, z) <=> forall(y, inductive(y) ==> in(t, y))))) by InstPredSchema(Map(P -> lambda(x, inductive(x))))(intersectionOfPredicateClassExists)
    have(() |- exists(z, forall(t, in(t, z) <=> forall(y, inductive(y) ==> in(t, y))))) by Cut(inductiveSetExists, inductExt)
  }

  /**
   * Theorem --- The intersection of all inductive sets is unique
   */
  val inductiveIntersectionUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> forall(y, inductive(y) ==> in(t, y))))
  ) {
    val prop = forall(y, inductive(y) ==> in(t, y))
    val fprop = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop) |- existsOne(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniqueByExtension)
    val existsLhs = have(() |- exists(z, fprop)) by Rewrite(inductiveIntersectionExistence)

    have(() |- existsOne(z, fprop)) by Cut(existsLhs, existsRhs)
  }

  /**
   * Natural Numbers (Inductive definition) --- The intersection of all
   * inductive sets is the set of natural numbers, N.
   */
  val naturalsInductive = DEF() --> The(z, forall(t, in(t, z) <=> (forall(y, inductive(y) ==> in(t, y)))))(inductiveIntersectionUniqueness)

  /**
   * Theorem --- Natural numbers form an inductive set
   */
  val naturalsAreInductive = makeTHM(
    () |- inductive(naturalsInductive())
  ) {
    val defHypo = have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) by Hypothesis

    // emptySet is in N
    have(() |- inductive(x) ==> in(emptySet(), x)) by Weakening(inductive.definition)
    val inductEmpty = thenHave(() |- forall(x, inductive(x) ==> in(emptySet(), x))) by RightForall

    val defEmpty =
      have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(emptySet(), z) <=> (forall(x, inductive(x) ==> in(emptySet(), x))))) by InstantiateForall(emptySet())(defHypo)

    have(
      forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(emptySet(), z) <=> (forall(x, inductive(x) ==> in(emptySet(), x)))) /\ forall(x, inductive(x) ==> in(emptySet(), x))
    ) by RightAnd(defEmpty, inductEmpty)
    val baseCase = thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- in(emptySet(), z)) by Trivial

    // if y in N, then succ y in N
    have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) by InstantiateForall(t)(defHypo)
    thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) by Weakening
    thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (forall(x, inductive(x) ==> in(t, x)))) by Trivial
    thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (inductive(x) ==> in(t, x))) by InstantiateForall(x)
    val inInductive = thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x)) by Restate

    have(inductive(x) |- forall(t, in(t, x) ==> in(successor(t), x))) by Weakening(inductive.definition)
    val inInductiveDef = thenHave(inductive(x) |- in(t, x) ==> in(successor(t), x)) by InstantiateForall(t)

    have(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x) /\ (in(t, x) ==> in(successor(t), x))) by RightAnd(inInductive, inInductiveDef)
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(successor(t), x)) by Trivial
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- inductive(x) ==> in(successor(t), x)) by Restate
    val succInst = thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- forall(x, inductive(x) ==> in(successor(t), x))) by RightForall

    val nDefSucc =
      have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(successor(t), z) <=> (forall(x, inductive(x) ==> in(successor(t), x))))) by InstantiateForall(successor(t))(defHypo)
    have(
      Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- forall(x, inductive(x) ==> in(successor(t), x)) /\ (in(successor(t), z) <=> (forall(
        x,
        inductive(x) ==> in(successor(t), x)
      )))
    ) by RightAnd(succInst, nDefSucc)
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- in(successor(t), z)) by Trivial
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) |- in(t, z) ==> in(successor(t), z)) by Restate
    val inductiveCase = thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- forall(t, in(t, z) ==> in(successor(t), z))) by RightForall

    have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- in(emptySet(), z) /\ forall(t, in(t, z) ==> in(successor(t), z))) by RightAnd(baseCase, inductiveCase)

    val form = formulaVariable
    val inductIff = thenHave(
      Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), inductive(z) <=> (in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))) |- inductive(z)
    ) by RightSubstIff(List((inductive(z), in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))), lambda(form, form))

    val inductDef = have(() |- inductive(z) <=> (in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))) by InstFunSchema(Map(x -> z))(inductive.definition)

    have(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) |- inductive(z)) by Cut(inductDef, inductIff)
    val inductExpansion =
      thenHave(Set(forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) |- inductive(naturalsInductive())) by InstFunSchema(Map(z -> naturalsInductive()))

    have(() |- (naturalsInductive() === naturalsInductive()) <=> forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) by InstantiateForall(naturalsInductive())(
      naturalsInductive.definition
    )
    val natDef = thenHave(() |- forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) by Rewrite

    have(() |- inductive(naturalsInductive())) by Cut(natDef, inductExpansion)
  }

  /**
   * Chapter 2
   * Ordinal Numbers
   */

  /**
   * Linear and Partial Ordering
   */

  /**
   * Partial Order --- `r` is a partial order on `x` if it is a [[reflexive]]
   * and [[transitive]] binary [[relation]] on `x`.
   */
  val partialOrder = DEF(r, x) --> relation(r, x) /\ antiReflexive(r, x) /\ transitive(r, x)

  // properties of elements under partial orders

  /**
   * Maximal Element --- `a` is a maximal element of `y` with respect to `r`,
   * which is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. ! a r b`
   */
  val maximalElement = DEF(a, y, r, x) --> partialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ forall(b, in(b, y) ==> (!in(pair(a, b), r)))

  /**
   * Minimal Element --- `a` is a minimal element of `y` with respect to `r`,
   * which is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. ! b r a`
   */
  val minimalElement = DEF(a, y, r, x) --> partialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ forall(b, in(b, y) ==> (!in(pair(b, a), r)))

  /**
   * Greatest Element --- `a` is the greatest element of `y` with respect to
   * `r`, which is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. b r a ⋁ b = a`
   */
  val greatestElement = DEF(a, y, r, x) --> partialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ forall(b, in(b, y) ==> (in(pair(b, a), r) \/ (a === b)))

  /**
   * Least Element --- `a` is the least element of `y` with respect to `r`,
   * which is a partial order on `x`, and `y ⊆ x`
   *
   *    `∀ b ∈ y. a r b ⋁ b = a`
   */
  val leastElement = DEF(a, y, r, x) --> partialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ forall(b, in(b, y) ==> (in(pair(a, b), r) \/ (a === b)))

  /**
   * Upper Bound --- `a` is an upper bound on `y` with respect to `r`, which is
   * a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. b r a ⋁ b = a`
   *
   * Note that as opposed to the greatest element, `a` is not enforced to be an
   * element of `y`.
   */
  val upperBound = DEF(a, y, r, x) --> partialOrder(r, x) /\ subset(y, x) /\ forall(b, in(b, y) ==> (in(pair(b, a), r) \/ (a === b)))

  /**
   * Lower Bound --- `a` is a lower bound on `y` with respect to `r`, which is a
   * partial order on `x`, and `y ⊆ x`
   *
   *    `∀ b ∈ y. a r b ⋁ b = a`
   *
   * Note that as opposed to the least element, `a` is not enforced to be an
   * element of `y`
   */
  val lowerBound = DEF(a, y, r, x) --> partialOrder(r, x) /\ subset(y, x) /\ forall(b, in(b, y) ==> (in(pair(a, b), r) \/ (a === b)))

  // val setOfLowerBounds = DEF(y, r, x) --> The(z, forall(t, in(t, z) <=> (in(t, x) /\ lowerBound(t, y, r, x))))(uniqueComprehension(x, lambda(Seq(t, x), lowerBound(t, y, r, x)))._2)

}
