package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.mathematics.FirstOrderLogic.*

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
  private val p = variable
  private val q = variable
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
    thenHave(fprop(z) /\ fprop(a) |- (a === z)) by Tautology
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
    * Theorem --- a set is an element of `x \cup y` iff it is an element of `x` or `y`
    */
  val setUnionMembership = makeTHM(
    () |- in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))
  ) {
    have(() |- forall(z, (z === setUnion(x, y)) <=> (z === union(unorderedPair(x, y))))) by Rewrite(setUnion.definition)
    thenHave(() |- (setUnion(x, y) === setUnion(x, y)) <=> (setUnion(x, y) === union(unorderedPair(x, y)))) by InstantiateForall(setUnion(x, y))
    val unionDef = thenHave(() |- (setUnion(x, y) === union(unorderedPair(x, y)))) by Restate

    val upairax = have(() |- in(a, unorderedPair(x, y)) <=> ((a === x) \/ (a === y))) by Rewrite(pairAxiom of (z -> a))
    val ta = have(() |- in(z, union(unorderedPair(x, y))) <=> exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Rewrite(unionAxiom of (z -> unorderedPair(x, y), x -> z))

    have(thesis) subproof {
      // the proof proceeds by showing that the existence criterion reduces to the RHS of the iff in the thesis

      val fwd = have(() |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) ==> (in(z, x) \/ in(z, y))) subproof {
        have(Set(in(z, a), a === x) |- in(z, a)) by Hypothesis
        val tax = thenHave(Set(in(z, a), a === x) |- in(z, x)) by RightSubstEq(List((a, x)), lambda(a, in(z, a)))

        have(Set(in(z, a), a === y) |- in(z, a)) by Hypothesis
        val tay = thenHave(Set(in(z, a), a === y) |- in(z, y)) by RightSubstEq(List((a, y)), lambda(a, in(z, a)))

        have(Set(in(z, a), (a === x) \/ (a === y)) |- Set(in(z, x), in(z, y))) by LeftOr(tax, tay)
        andThen(applySubst(upairax, false))
        thenHave(Set(in(z, a) /\ in(a, unorderedPair(x, y))) |- Set(in(z, x), in(z, y))) by Restate
        thenHave(exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) |- Set(in(z, x), in(z, y))) by LeftExists
        thenHave(thesis) by Restate
      }

      val bwd = have(() |- ((in(z, x) \/ in(z, y)) ==> exists(a, in(z, a) /\ in(a, unorderedPair(x, y))))) subproof {
        have(Set(in(z, x), (a === x)) |- in(z, x)) by Hypothesis
        thenHave(Set(in(z, x), (a === x)) |- in(z, a)) by RightSubstEq(List((a, x)), lambda(a, in(z, a)))
        thenHave(Set(in(z, x), (a === x)) |- in(z, a) /\ ((a === x) \/ (a === y))) by Tautology
        andThen(applySubst(upairax, false))
        thenHave(Set(in(z, x), (a === x)) |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by RightExists(a)
        thenHave(Set(in(z, x), (x === x)) |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by InstFunSchema(Map(a -> x))
        val tax = thenHave(Set(in(z, x)) |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Rewrite

        have(Set(in(z, y), (a === y)) |- in(z, y)) by Hypothesis
        thenHave(Set(in(z, y), (a === y)) |- in(z, a)) by RightSubstEq(List((a, y)), lambda(a, in(z, a)))
        thenHave(Set(in(z, y), (a === y)) |- in(z, a) /\ ((a === x) \/ (a === y))) by Tautology
        andThen(applySubst(upairax, false))
        thenHave(Set(in(z, y), (a === y)) |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by RightExists(a)
        thenHave(Set(in(z, y), (y === y)) |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by InstFunSchema(Map(a -> y))
        val tay = thenHave(Set(in(z, y)) |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate

        have((in(z, x) \/ in(z, y)) |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by LeftOr(tax, tay)
        thenHave(thesis) by Restate
      }

      val existsSubst = have(() |- exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> (in(z, x) \/ in(z, y))) by RightIff(fwd, bwd)
      
      have(() |- in(z, union(unorderedPair(x, y))) <=> exists(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Rewrite(ta)
      andThen(applySubst(existsSubst))
      andThen(applySubst(unionDef))
    }

  }

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
    thenHave(forall(y, !in(y, x)) |- (x === emptySet())) by Tautology
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
    thenHave(() |- subset(emptySet(), x)) by Tautology
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
    val emptyinPower = thenHave(() |- in(emptySet(), powerSet(x))) by Tautology
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

    thenHave((z === x) |- in(z, unorderedPair(x, y))) by Tautology
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

    thenHave((z === y) |- in(z, unorderedPair(x, y))) by Tautology
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
    thenHave(in(z, union(X)) |- exists(y, in(z, y) /\ in(y, X))) by Tautology

    val andLhs = have(() |- in(x, X)) by InstFunSchema(Map(y -> x))(firstElemInPair)
    val andRhs = have(in(z, x) |- in(z, x)) by Hypothesis
    have(in(z, x) |- in(z, x) /\ in(x, X)) by RightAnd(andLhs, andRhs)
    val fwdLhs = thenHave(in(z, x) |- exists(y, in(z, y) /\ in(y, X))) by RightExists(x)
    have(in(z, x) |- exists(y, in(z, y) /\ in(y, X)) /\ (in(z, union(X)) <=> exists(y, in(z, y) /\ in(y, X)))) by RightAnd(fwdLhs, unionAx)
    thenHave(in(z, x) |- in(z, union(X))) by Tautology
    val fwd = thenHave(() |- in(z, x) ==> in(z, union(X))) by Rewrite

    // backward direction
    //  z ∈ ∪ X |- z ∈ x

    have(in(y, X) |- in(y, X)) by Hypothesis
    val bwdHypo = thenHave(in(z, y) /\ in(y, X) |- in(y, X)) by Weakening
    have(in(z, y) /\ in(y, X) |- in(y, X) /\ (in(y, X) <=> (x === y))) by RightAnd(bwdHypo, singletonHasNoExtraElements)
    val cutLhs = thenHave(in(z, y) /\ in(y, X) |- (x === y)) by Tautology

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
    thenHave(() |- (union(X) === x)) by Tautology
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
    val lhs = thenHave(() |- in(x, singleton(x))) by Tautology

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
    thenHave((singleton(x) === singleton(y)) |- forall(z, in(z, singleton(x)) <=> in(z, singleton(y)))) by Tautology
    val singiff = thenHave((singleton(x) === singleton(y)) |- in(z, singleton(x)) <=> in(z, singleton(y))) by InstantiateForall(z)

    val singX = have(() |- in(z, singleton(x)) <=> (z === x)) by InstFunSchema(Map(y -> z))(singletonHasNoExtraElements)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(x)) <=> in(z, singleton(y))) /\ (in(z, singleton(x)) <=> (z === x))) by RightAnd(singiff, singX)
    val yToX = thenHave((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x))) by Trivial

    val singY = have(() |- in(z, singleton(y)) <=> (z === y)) by InstFunSchema(Map(x -> y))(singX)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x)) /\ (in(z, singleton(y)) <=> (z === y))) by RightAnd(yToX, singY)
    thenHave((singleton(x) === singleton(y)) |- ((z === x) <=> (z === y))) by Trivial
    thenHave((singleton(x) === singleton(y)) |- ((x === x) <=> (x === y))) by InstFunSchema(Map(z -> x))

    thenHave((singleton(x) === singleton(y)) |- (x === y)) by Rewrite
    val fwd = thenHave(() |- (singleton(x) === singleton(y)) ==> (x === y)) by Tautology

    // backward direction
    //  x === y |- {x} === {y}
    have(() |- singleton(x) === singleton(x)) by RightRefl
    thenHave((x === y) |- singleton(x) === singleton(y)) by RightSubstEq(List((x, y)), lambda(a, singleton(x) === singleton(a)))
    val bwd = thenHave(() |- (x === y) ==> (singleton(x) === singleton(y))) by Rewrite

    have(() |- (singleton(x) === singleton(y)) <=> (x === y)) by RightIff(fwd, bwd)
  }

  /**
    * Theorem --- Unordered pairs of elements of a set `x` are in its power set `P(x)`.
    */
  val unorderedPairInPowerSet = makeTHM(
    () |- (in(a, x) /\ in(b, x)) <=> in(unorderedPair(a, b), powerSet(x))
  ) {

    // forward
    val fwd = have(() |- (in(a, x) /\ in(b, x)) ==> in(unorderedPair(a, b), powerSet(x))) subproof {
    val axExpansion = have(() |- in(unorderedPair(a, b), powerSet(x)) <=> forall(z, in(z, unorderedPair(a, b)) ==> in(z, x))) by Tautology.from(powerAxiom of (x -> unorderedPair(a, b), y -> x), subsetAxiom of (x -> unorderedPair(a, b), y -> x))

    val abToz = have(in(a, x) /\ in(b, x) |- forall(z, in(z, unorderedPair(a, b)) ==> in(z, x))) subproof {
      val pairAxab = have(in(z, unorderedPair(a, b)) |- (z === a) \/ (z === b)) by Tautology.from(pairAxiom of (x -> a, y -> b))

      have(in(a, x) /\ in(b, x) |- in(a, x)) by Restate
      val za = thenHave(Set(in(a, x) /\ in(b, x), (z === a)) |- in(z, x)) by RightSubstEq(List((z, a)), lambda(a, in(a, x)))
      have(in(a, x) /\ in(b, x) |- in(b, x)) by Restate
      val zb = thenHave(Set(in(a, x) /\ in(b, x), (z === b)) |- in(z, x)) by RightSubstEq(List((z, b)), lambda(a, in(a, x)))

      val zab = have(Set(in(a, x) /\ in(b, x), (z === a) \/ (z === b)) |- in(z, x)) by LeftOr(za, zb)

      have(Set(in(z, unorderedPair(a, b)), in(a, x) /\ in(b, x)) |- in(z, x)) by Cut(pairAxab, zab)
      thenHave(in(a, x) /\ in(b, x) |- in(z, unorderedPair(a, b)) ==> in(z, x)) by Restate
      thenHave(thesis) by RightForall
    }

      have(thesis) by Tautology.from(abToz, axExpansion)
    }

    val bwd = have(() |- in(unorderedPair(a, b), powerSet(x)) ==> (in(a, x) /\ in(b, x))) subproof {
      have(in(unorderedPair(a, b), powerSet(x)) |- forall(z, in(z, unorderedPair(a, b)) ==> in(z, x))) by Tautology.from(powerAxiom of (x -> unorderedPair(a, b), y -> x), subsetAxiom of (x -> unorderedPair(a, b), y -> x))
      val upz = thenHave(in(unorderedPair(a, b), powerSet(x)) |- in(z, unorderedPair(a, b)) ==> in(z, x)) by InstantiateForall(z)

      val xa = have(in(unorderedPair(a, b), powerSet(x)) |- in(a, x)) by Tautology.from(upz of (z -> a), firstElemInPair of (x -> a, y -> b))
      val xb = have(in(unorderedPair(a, b), powerSet(x)) |- in(b, x)) by Tautology.from(upz of (z -> b), secondElemInPair of (x -> a, y -> b))
      have(in(unorderedPair(a, b), powerSet(x)) |- in(b, x) /\ in(a, x)) by RightAnd(xa, xb)
      thenHave(thesis) by Restate
    }

    have(thesis) by RightIff(fwd, bwd)
  }

  /**
   * Theorem --- Pair Extensionality
   * 
   * Two ordered pairs are equal iff their elements are equal when taken in order.
   *
   *  pair(a, b) === {{a}, {a, b}}
   *
   *  pair(a, b) === pair(c, d) iff a === c and b === d
   */
  val pairExtensionality = makeTHM(
      () |- (pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))
  ) {
      // forward direction
      //  (a === c) /\ (b === d) ==> pair a b === pair c d
      val fwd = have(() |- ((a === c) /\ (b === d)) ==> (pair(a, b) === pair(c, d))) subproof {
        have(() |- (pair(a, b) === pair(a, b))) by RightRefl
        thenHave(Set((a === c), (b === d)) |- (pair(a, b) === pair(c, d))) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(x, y), pair(a, b) === pair(x, y)))
        thenHave(thesis) by Rewrite
      }

      // backward direction
      //  pair a b === pair c d ==> (a === c) /\ (b === d)
      val bwd = have(() |- (pair(a, b) === pair(c, d)) ==> ((a === c) /\ (b === d))) subproof {
      have(Set((pair(a, b) === pair(c, d))) |- (pair(a, b) === pair(c, d))) by Hypothesis
      val lhs1 = thenHave(Set((pair(a, b) === pair(c, d)), (unorderedPair(unorderedPair(a, b), singleton(a)) === unorderedPair(unorderedPair(c, d), singleton(c))) <=> (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(c))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(a) === unorderedPair(c, d))))) |- (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(c))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(a) === unorderedPair(c, d))))) by RightSubstIff(List(((unorderedPair(unorderedPair(a, b), singleton(a)) === unorderedPair(unorderedPair(c, d), singleton(c))), (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(c))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(a) === unorderedPair(c, d)))))), lambda(h, h))
      have(Set((pair(a, b) === pair(c, d))) |- (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(c))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(a) === unorderedPair(c, d))))) by Cut(unorderedPairExtensionality of (a -> unorderedPair(a, b), b -> singleton(a), c -> unorderedPair(c, d), d -> singleton(c)), lhs1)
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> b, c -> c, d -> d))) // {a, b} = {c, d}
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> a, c -> c, d -> d))) //    {a} = {c, d}
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> b, c -> c, d -> c))) // {a, b} = {c}
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> a, c -> c, d -> c))) //    {a} = {c}
      val expandedProp = thenHave(Set((pair(a, b) === pair(c, d))) |- ((((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))) /\ (((a === c) /\ (a === c)) \/ ((a === c) /\ (a === c)))) \/ ((((a === c) /\ (b === c)) \/ ((a === c) /\ (b === c))) /\ (((a === c) /\ (a === d)) \/ ((a === d) /\ (a === c))))) by Restate
      val ac = thenHave(Set((pair(a, b) === pair(c, d))) |- (a === c)) by Tautology

      // required subproof, transitivity of equality
      // b = c, a = d, a = c |- b = d
      val transEqdb = have(Set(d === a, a === c, c === b) |- d === b) subproof {
        val dac = have((d === a) /\ (a === c) |- (d === c)) by Rewrite(equalityTransitivity of (x -> d, y -> a, z -> c))
        have((d === c) /\ (c === b) |- (d === b)) by Rewrite(equalityTransitivity of (x -> d, y -> c, z -> b))
        val dcb = thenHave(Set((d === c), (c === b)) |- (d === b)) by Restate
        val db = have(Set((d === a) /\ (a === c), (c === b)) |- (d === b)) by Cut(dac, dcb)

        thenHave(thesis) by Restate
      }

      val db = have(Set((pair(a, b) === pair(c, d))) |- (a === c) /\ (b === d)) by Tautology.from(expandedProp, ac, transEqdb)
      thenHave(thesis) by Restate
    }

      have(thesis) by RightIff(fwd, bwd)
  }

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
    val innerRhs = thenHave(in(y, X) |- (x === y)) by Tautology

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
    val contraLhs = thenHave(subset(powerSet(x), x) |- in(powerSet(x), powerSet(x))) by Tautology

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
    thenHave(forall(y, P(y) ==> in(t, y)) /\ P(x) |- in(t, x) /\ forall(y, P(y) ==> in(t, y))) by Tautology
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
  val firstInPair = DEF(p) --> union(unaryIntersection(p))

  val secondInPairSingletonUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))
  ) {
    have(thesis) by UniqueComprehension(union(p), lambda(Seq(t, x), ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p))))))
  }

  /**
   * See [[secondInPair]].
   */
  val secondInPairSingleton =
    DEF(p) --> The(z, forall(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))(secondInPairSingletonUniqueness)

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
  val secondInPair = DEF(p) --> union(secondInPairSingleton(p))

  /**
   * Cartesian Products and Relations
   */

  val cartesianProductUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))
  ) {
    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))) by UniqueComprehension(
      powerSet(powerSet(setUnion(x, y))),
      lambda(Seq(t, z), exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))
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
    DEF(x, y) --> The(z, forall(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))(cartesianProductUniqueness)


  /**
    * Theorem --- a pair is in the set `x * y` iff its elements are in `x` and
    * `y` respectively.
    */
  val pairInCartesianProduct = makeTHM(
    () |- in(pair(a, b), cartesianProduct(x, y)) <=> (in(a, x) /\ in(b, y))
  ) {
    have(() |- (cartesianProduct(x, y) === cartesianProduct(x, y)) <=> forall(t, in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ exists(c, exists(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y)))))) by InstantiateForall(cartesianProduct(x, y))(cartesianProduct.definition)
    thenHave(() |- forall(t, in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ exists(c, exists(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y)))))) by Rewrite
    val cartProdDef = thenHave(() |- in(pair(a, b), cartesianProduct(x, y)) <=> (in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) /\ exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y))))) by InstantiateForall(pair(a, b))

    // forward
    // (a, b) \in x * y ==> a \in x /\ b \in y
    val fwd = have(() |- in(pair(a, b), cartesianProduct(x, y)) ==> (in(a, x) /\ in(b, y))) subproof {
      have(Set(a === c, b === d, in(c, x) /\ in(d, y)) |- in(c, x) /\ in(d, y)) by Hypothesis
      thenHave(Set(a === c, b === d, in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(a, b), in(a, x) /\ in(b, y)))
      thenHave(Set((a === c) /\ (b === d), in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by Restate
      andThen(applySubst(pairExtensionality))
      thenHave((pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y) |- in(a, x) /\ in(b, y)) by Restate
      thenHave(exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by LeftExists
      thenHave(exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(a, x) /\ in(b, y)) by LeftExists
      val cdExists = thenHave((in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) /\ exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(a, x) /\ in(b, y))) by Weakening
      have(thesis) by Tautology.from(cdExists, cartProdDef)
    }
    // backward
    // a \in x /\ b \in y ==> (a, b) \in x * y
    val bwd = have(() |- in(a, x) /\ in(b, y) ==> in(pair(a, b), cartesianProduct(x, y))) subproof {
      val membership = have(in(a, x) /\ in(b, y) |- in(pair(a, b), powerSet(powerSet(setUnion(x, y))))) subproof {
        val powerSubsetDef = have(() |- in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) <=> forall(z, in(z, pair(a, b)) ==> in(z, powerSet(setUnion(x, y))))) by Tautology.from(powerAxiom of (x -> pair(a, b), y -> powerSet(setUnion(x, y))), subsetAxiom of (x -> pair(a, b), y -> powerSet(setUnion(x, y))))
      
        val unionToPower = have(Set(in(a, setUnion(x, y)) /\ in(b, setUnion(x, y)), in(z, pair(a, b))) |- in(z, powerSet(setUnion(x, y)))) subproof {
          val zabHypo = have(in(z, pair(a, b)) |- in(z, pair(a, b))) by Hypothesis
          val cutLhs = have(in(z, pair(a, b)) |- (z === unorderedPair(a, b)) \/ (z === singleton(a))) by Tautology.from(zabHypo, pairAxiom of (x -> unorderedPair(a, b), y -> singleton(a)))

          // need to show that {a, b} and {a} = {a, a} are in P(x \cup y)
          val prem = (in(a, setUnion(x, y)) /\ in(b, setUnion(x, y)))

          have(prem |- in(unorderedPair(a, b), powerSet(setUnion(x, y)))) by Weakening(unorderedPairInPowerSet of (x -> setUnion(x, y)))
          val zab = thenHave(Set(prem, (z === unorderedPair(a, b))) |- in(z, powerSet(setUnion(x, y)))) by RightSubstEq(List((z, unorderedPair(a, b))), lambda(a, in(a, powerSet(setUnion(x, y)))))
          have(prem |- in(unorderedPair(a, a), powerSet(setUnion(x, y)))) by Weakening(unorderedPairInPowerSet of (x -> setUnion(x, y), b -> a))
          val zaa = thenHave(Set(prem, (z === unorderedPair(a, a))) |- in(z, powerSet(setUnion(x, y)))) by RightSubstEq(List((z, unorderedPair(a, a))), lambda(a, in(a, powerSet(setUnion(x, y)))))

          val cutRhs = have(Set(prem, (z === unorderedPair(a, b)) \/ (z === singleton(a))) |- in(z, powerSet(setUnion(x, y)))) by LeftOr(zab, zaa)

          have(thesis) by Cut(cutLhs, cutRhs)
        }

        val abToUnion = have(in(a, x) /\ in(b, y) |- in(a, setUnion(x, y)) /\ in(b, setUnion(x, y))) subproof {
          have(in(a, x) |- in(a, setUnion(x, y)) <=> (in(a, x) \/ in(a, y))) by Weakening(setUnionMembership of (z -> a))
          val aUn = thenHave(in(a, x) |- in(a, setUnion(x, y))) by Tautology
          have(in(b, y) |- in(b, setUnion(x, y)) <=> (in(b, x) \/ in(b, y))) by Weakening(setUnionMembership of (z -> b))
          val bUn = thenHave(in(b, y) |- in(b, setUnion(x, y))) by Tautology

          have(Set(in(a, x), in(b, y)) |- in(a, setUnion(x, y)) /\ in(b, setUnion(x, y))) by RightAnd(aUn, bUn)
          thenHave(thesis) by Restate
        }

        have(Set(in(a, x) /\ in(b, y), in(z, pair(a, b))) |- in(z, powerSet(setUnion(x, y)))) by Cut(abToUnion, unionToPower)
        thenHave(Set(in(a, x) /\ in(b, y)) |- in(z, pair(a, b)) ==> in(z, powerSet(setUnion(x, y)))) by Restate
        val abToPower = thenHave(Set(in(a, x) /\ in(b, y)) |- forall(z, in(z, pair(a, b)) ==> in(z, powerSet(setUnion(x, y))))) by RightForall

        have(thesis) by Tautology.from(abToPower, powerSubsetDef)
      }

      val filtering = have(in(a, x) /\ in(b, y) |- exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)))) subproof {
        have(in(a, x) /\ in(b, y) |- (pair(a, b) === pair(a, b)) /\ in(a, x) /\ in(b, y)) by Restate
        thenHave(in(a, x) /\ in(b, y) |- exists(d, (pair(a, d) === pair(a, b)) /\ in(a, x) /\ in(d, y))) by RightExists(b)
        thenHave(in(a, x) /\ in(b, y) |- exists(c, exists(d, (pair(c, d) === pair(a, b)) /\ in(c, x) /\ in(d, y)))) by RightExists(a)
      }

      val compCriterion = have(in(a, x) /\ in(b, y) |- in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) /\ exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)))) by RightAnd(membership, filtering)

      have(thesis) by Tautology.from(compCriterion, cartProdDef)
    }

    have(thesis) by RightIff(fwd, bwd)
  }

  val pairInSetImpliesPairInUnion = makeTHM(
    in(pair(a, b), r) |- in(a, union(union(r))) /\ in(b, union(union(r)))
  ) {
    // a, b in {a, b} and union union r
    // {a, b} in union r
    // pair a b in r
    val unionUP = have(in(pair(a, b), r) |- in(unorderedPair(a, b), union(r))) subproof {
      val hypo = have(in(pair(a, b), r) |- in(pair(a, b), r)) by Hypothesis
      have(in(pair(a, b), r) |- in(unorderedPair(a, b), pair(a, b)) /\ in(pair(a, b), r)) by RightAnd(hypo, firstElemInPair of (x -> unorderedPair(a, b), y -> singleton(a)))
      thenHave(in(pair(a, b), r) |- exists(y, in(unorderedPair(a, b), y) /\ in(y, r))) by RightExists(pair(a, b))
      andThen(applySubst(unionAxiom of (x -> unorderedPair(a, b), z -> r)))
    }
    val unionA = have(in(unorderedPair(a, b), union(r)) |- in(a, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(a, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, firstElemInPair of (x -> a, y -> b))
      thenHave(in(unorderedPair(a, b), union(r)) |- exists(y, in(a, y) /\ in(y, union(r)))) by RightExists(unorderedPair(a, b))
      andThen(applySubst(unionAxiom of (x -> a, z -> union(r))))
    }
    val unionB = have(in(unorderedPair(a, b), union(r)) |- in(b, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(b, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, secondElemInPair of (x -> a, y -> b))
      thenHave(in(unorderedPair(a, b), union(r)) |- exists(y, in(b, y) /\ in(y, union(r)))) by RightExists(unorderedPair(a, b))
      andThen(applySubst(unionAxiom of (x -> b, z -> union(r))))
    }

    have(thesis) by Tautology.from(unionUP, unionA, unionB)
  }

  /**
   * Binary Relation --- A binary relation `r` from `a` to `b` is a subset of
   * the [[cartesianProduct]] of `a` and `b`, `a * b`. We say `x r y`, `r(x,
   * y)`, or `r relates x to y` for `(x, y) ∈ r`.
   */
  val relationBetween = DEF (r, a, b) --> subset(r, cartesianProduct(a, b))

  /**
   * `r` is a relation *from* `a` if there exists a set `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relationFrom = DEF(r, a) --> exists(b, relationBetween(r, a, b))

  /**
   * `r` is a relation if there exist sets `a` and `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relation = DEF(r) --> exists(a, exists(b, subset(r, cartesianProduct(a, b))))

  val relationDomainUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> exists(a, in(pair(t, a), r))))
  ) {
    val uniq = have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))) by UniqueComprehension(union(union(r)), lambda(Seq(t, b), exists(a, in(pair(t, a), r))))

    // eliminating t \in UU r
    // since it is implied by the second condition
    val transform = have(exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r))))) |- exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(t, a), r)))))) subproof {
      val hypo = have(in(pair(t, a), r) |- in(pair(t, a), r)) by Hypothesis
      have(in(pair(t, a), r) |- in(t, union(union(r))) /\ in(a, union(union(r)))) by Cut(hypo, pairInSetImpliesPairInUnion of (a -> t, b -> a))
      thenHave(in(pair(t, a), r) |- in(t, union(union(r)))) by Weakening
      thenHave(exists(a, in(pair(t, a), r)) |- in(t, union(union(r)))) by LeftExists
      val lhs = thenHave(() |- exists(a, in(pair(t, a), r)) ==> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) by Tautology
      val rhs = have(() |- (exists(a, in(pair(t, a), r)) /\ in(t, union(union(r)))) ==> exists(a, in(pair(t, a), r))) by Restate

      val subst = have(() |- exists(a, in(pair(t, a), r)) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) by RightIff(lhs, rhs)

      have(Set(in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) |- in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) by Hypothesis
      val cutRhs = thenHave(Set(in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r))), exists(a, in(pair(t, a), r)) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) |- in(t, z) <=> (exists(a, in(pair(t, a), r)))) by RightSubstIff(List((exists(a, in(pair(t, a), r)), in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))), lambda(h, in(t, z) <=> h))
      have(Set(in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) |- in(t, z) <=> (exists(a, in(pair(t, a), r)))) by Cut(subst, cutRhs)
      thenHave(forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) |- in(t, z) <=> (exists(a, in(pair(t, a), r)))) by LeftForall(t)
      thenHave(forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) |- forall(t, in(t, z) <=> (exists(a, in(pair(t, a), r))))) by RightForall
      thenHave(forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))) |- exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(t, a), r)))))) by RightExists(z)
      thenHave(thesis) by LeftExists
    }

    // converting the exists to existsOne
    val cutL = have(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r))))) |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))) by Rewrite(existsOneImpliesExists of (P -> lambda(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))))
    val cutR = have(exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(t, a), r))))) |- existsOne(z, forall(t, in(t, z) <=> (exists(a, in(pair(t, a), r)))))) by Rewrite(uniqueByExtension of (schemPred -> lambda(t, (exists(a, in(pair(t, a), r))))))

    val trL = have(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r))))) |- exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(t, a), r)))))) by Cut(cutL, transform)
    val trR = have(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r))))) |- existsOne(z, forall(t, in(t, z) <=> (exists(a, in(pair(t, a), r)))))) by Cut(trL, cutR) 

    have(thesis) by Cut.withParameters(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r))))))(uniq, trR)
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
  val relationDomain = DEF(r) --> The(z, forall(t, in(t, z) <=> exists(a, in(pair(t, a), r))))(relationDomainUniqueness)

  val relationRangeUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> exists(a, in(pair(a, t), r))))
  ) {
    val uniq = have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))) by UniqueComprehension(union(union(r)), lambda(Seq(t, b), exists(a, in(pair(a, t), r))))

    // eliminating t \in UU r
    // since it is implied by the second condition
    val transform = have(exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r))))) |- exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(a, t), r)))))) subproof {
      val hypo = have(in(pair(a, t), r) |- in(pair(a, t), r)) by Hypothesis
      have(in(pair(a, t), r) |- in(t, union(union(r))) /\ in(a, union(union(r)))) by Cut(hypo, pairInSetImpliesPairInUnion of (a -> a, b -> t))
      thenHave(in(pair(a, t), r) |- in(t, union(union(r)))) by Weakening
      thenHave(exists(a, in(pair(a, t), r)) |- in(t, union(union(r)))) by LeftExists
      val lhs = thenHave(() |- exists(a, in(pair(a, t), r)) ==> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) by Tautology
      val rhs = have(() |- (exists(a, in(pair(a, t), r)) /\ in(t, union(union(r)))) ==> exists(a, in(pair(a, t), r))) by Restate

      val subst = have(() |- exists(a, in(pair(a, t), r)) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) by RightIff(lhs, rhs)

      have(Set(in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) |- in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) by Hypothesis
      val cutRhs = thenHave(Set(in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r))), exists(a, in(pair(a, t), r)) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) |- in(t, z) <=> (exists(a, in(pair(a, t), r)))) by RightSubstIff(List((exists(a, in(pair(a, t), r)), in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))), lambda(h, in(t, z) <=> h))
      have(Set(in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) |- in(t, z) <=> (exists(a, in(pair(a, t), r)))) by Cut(subst, cutRhs)
      thenHave(forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) |- in(t, z) <=> (exists(a, in(pair(a, t), r)))) by LeftForall(t)
      thenHave(forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) |- forall(t, in(t, z) <=> (exists(a, in(pair(a, t), r))))) by RightForall
      thenHave(forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))) |- exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(a, t), r)))))) by RightExists(z)
      thenHave(thesis) by LeftExists
    }

    // converting the exists to existsOne
    val cutL = have(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r))))) |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))) by Rewrite(existsOneImpliesExists of (P -> lambda(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))))
    val cutR = have(exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(a, t), r))))) |- existsOne(z, forall(t, in(t, z) <=> (exists(a, in(pair(a, t), r)))))) by Rewrite(uniqueByExtension of (schemPred -> lambda(t, (exists(a, in(pair(a, t), r))))))

    val trL = have(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r))))) |- exists(z, forall(t, in(t, z) <=> (exists(a, in(pair(a, t), r)))))) by Cut(cutL, transform)
    val trR = have(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r))))) |- existsOne(z, forall(t, in(t, z) <=> (exists(a, in(pair(a, t), r)))))) by Cut(trL, cutR) 

    have(thesis) by Cut.withParameters(existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r))))))(uniq, trR)
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
  val relationRange = DEF(r) --> The(z, forall(t, in(t, z) <=> exists(a, in(pair(a, t), r))))(relationRangeUniqueness)

  /**
   * (Binary) Relation Field --- The union of the domain and range of a
   * relation, or the set of all elements related by `r`.
   *
   * @param r relation (set)
   */
  val relationField = DEF(r) --> (setUnion(relationDomain(r), relationRange(r)))

  /**
   * Functional --- A binary [[relation]] is functional if it maps every element in its domain 
   * to a unique element (in its range).
   *
   *     `functional(f) ⇔ relation(f) /\ \forall x. (\exists y. (x, y) \in f) \Rightarrow (\exists! y. (x, y) \in f)`
   *
   * We may alternatively denote `(z, y) ∈ f` as `y = f(z)`.
   *
   * @param f relation (set)
   */
  val functional = DEF(f) --> relation(f) /\ forall(x, exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f)))

  /**
   * Functional Over a Set --- A binary [[relation]] is functional over a set `x` if it is
   * [[functional]] and has`x` as its domain ([[relationDomain]]).
   *
   * @param f relation (set)
   * @param x set
   */
  val functionalOver = DEF(f, x) --> functional(f) /\ (relationDomain(f) === x)

  val setOfFunctionsUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))
  ) {
    have(thesis) by UniqueComprehension(powerSet(cartesianProduct(x, y)), lambda(Seq(t, z), functionalOver(t, x)))
  }

  /**
   * Set of functions --- All functions from `x` to `y`, denoted `x \to y` or
   * `\to(x, y)`.
   *
   * Since functions from `x` to `y` contain pairs of the form `(a, b) | a \in
   * x, b \in y`, it is a filtering on the power set of their product, i.e. `x
   * \to y \subseteq PP(x * y)`.
   */
  val setOfFunctions = DEF(x, y) --> The(z, forall(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))(setOfFunctionsUniqueness)

  /**
   * Function From (x to y) --- denoted  `f \in x \to y` or `f: x \to y`.
   */
  val functionFrom = DEF(f, x, y) --> in(f, setOfFunctions(x, y))

  /**
   * Theorem --- A function between two sets is [[functional]]
   */
  val functionFromImpliesFunctional = makeTHM(
    functionFrom(f, x, y) |- functional(f)
  ) {
    have(() |- forall(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(() |- in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    val funOver = have(functionFrom(f, x, y) |- functional(f)) by Tautology.from(funSetDef, functionFrom.definition, functionalOver.definition)
  }
  
  val functionApplicationUniqueness = makeTHM(
    () |- existsOne(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === emptySet())))
  ) {
    val prem = functional(f) /\ in(x, relationDomain(f))

    // we prove thesis by two cases, first by assuming prem, and then by assuming !prem

    // positive direction
    have(functional(f) |- forall(x, exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f)))) by Tautology.from(functional.definition)
    val funcDef = thenHave(functional(f) |- exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f))) by InstantiateForall(x)

    have(() |- (relationDomain(f) === relationDomain(f)) <=> forall(t, in(t, relationDomain(f)) <=> (exists(y, in(pair(t, y), f))))) by InstantiateForall(relationDomain(f))(relationDomain.definition of (r -> f))
    thenHave(() |- forall(t, in(t, relationDomain(f)) <=> (exists(y, in(pair(t, y), f))))) by Restate
    thenHave(() |- in(x, relationDomain(f)) <=> (exists(y, in(pair(x, y), f)))) by InstantiateForall(x)
    val domDef = thenHave(in(x, relationDomain(f)) |- exists(y, in(pair(x, y), f))) by Weakening

    val uniqPrem = have(functional(f) /\ in(x, relationDomain(f)) |- existsOne(z, in(pair(x, z), f))) by Tautology.from(funcDef, domDef)

    val positive = have(prem |- existsOne(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === emptySet()))))) subproof {
      val lhs = have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ top()))) subproof {
        val iff = have(prem |- (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) by Restate
        have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> in(pair(x, y), f))) by Restate
        val subst = thenHave(Set(prem /\ ((z === y) <=> in(pair(x, y), f)), (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by RightSubstIff(
          List(((in(pair(x, y), f)), (prem ==> in(pair(x, y), f)))),
          lambda(h, ((z === y) <=> h))
        )

        have(Set(prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have(Set(prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) subproof {
        val topIff = have(prem |- (!prem ==> (y === emptySet())) <=> top()) by RewriteTrue
        val topSubst = have(
          Set(prem /\ ((z === y) <=> in(pair(x, y), f)), ((!prem ==> (y === emptySet())) <=> top())) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))
        ) by RightSubstIff(List(((!prem ==> (y === emptySet())), top())), lambda(h, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ h))))(lhs)

        have(Set(prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) by Cut(topIff, topSubst)
        thenHave(Set(prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) by Restate
      }

      val quantification = have(Set(prem, existsOne(z, ((z === y) <=> in(pair(x, y), f)))) |- existsOne(z, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet())))))) subproof {
        have(Set(prem, forall(y, ((z === y) <=> in(pair(x, y), f)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) by LeftForall(y)(topIntro)
        thenHave(Set(prem, forall(y, ((z === y) <=> in(pair(x, y), f)))) |- forall(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet())))))) by RightForall
        thenHave(Set(prem, forall(y, ((z === y) <=> in(pair(x, y), f)))) |- exists(z, forall(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))))) by RightExists(z)
        thenHave(
          Set(prem, exists(z, forall(y, ((z === y) <=> in(pair(x, y), f))))) |- exists(z, forall(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))))
        ) by LeftExists
        thenHave(Set(prem, existsOne(z, in(pair(x, z), f))) |- existsOne(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === emptySet()))))) by Restate
      }

      have(thesis) by Cut(uniqPrem, quantification)
    }

    // negative
    have(() |- (emptySet() === y) <=> (emptySet() === y)) by Restate
    thenHave(() |- forall(y, (emptySet() === y) <=> (emptySet() === y))) by RightForall
    thenHave(() |- exists(z, forall(y, (z === y) <=> (emptySet() === y)))) by RightExists(emptySet())
    val emptyPrem = thenHave(() |- existsOne(z, (z === emptySet()))) by Restate

    val negative = have(!prem |- existsOne(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === emptySet()))))) subproof {
      val lhs = have(!prem /\ ((z === y) <=> (y === emptySet())) |- ((z === y) <=> ((!prem ==> (y === emptySet())) /\ top()))) subproof {
        val iff = have(!prem |- ((y === emptySet())) <=> (!prem ==> (y === emptySet()))) by Restate
        have(!prem /\ ((z === y) <=> (y === emptySet())) |- ((z === y) <=> (y === emptySet()))) by Restate
        val subst = thenHave(
          Set(!prem /\ ((z === y) <=> (y === emptySet())), ((y === emptySet())) <=> (!prem ==> (y === emptySet()))) |- ((z === y) <=> (!prem ==> (y === emptySet())))
        ) by RightSubstIff(List((((y === emptySet())), (!prem ==> (y === emptySet())))), lambda(h, ((z === y) <=> h)))

        have(Set(!prem /\ ((z === y) <=> (y === emptySet())), !prem) |- ((z === y) <=> (!prem ==> (y === emptySet())))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have(Set(!prem, ((z === y) <=> (y === emptySet()))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) subproof {
        val topIff = have(!prem |- (prem ==> in(pair(x, y), f)) <=> top()) by RewriteTrue
        val topSubst = have(
          Set(!prem /\ ((z === y) <=> (y === emptySet())), ((prem ==> in(pair(x, y), f)) <=> top())) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))
        ) by RightSubstIff(List(((prem ==> in(pair(x, y), f)), top())), lambda(h, ((z === y) <=> ((!prem ==> (y === emptySet())) /\ h))))(lhs)

        have(Set(!prem /\ ((z === y) <=> (y === emptySet())), !prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) by Cut(topIff, topSubst)
        thenHave(Set(!prem, ((z === y) <=> (y === emptySet()))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) by Restate
      }

      val quantification =
        have(Set(!prem, existsOne(z, ((z === y) <=> (y === emptySet())))) |- existsOne(z, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet())))))) subproof {
          have(Set(!prem, forall(y, ((z === y) <=> (y === emptySet())))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))) by LeftForall(y)(topIntro)
          thenHave(Set(!prem, forall(y, ((z === y) <=> (y === emptySet())))) |- forall(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet())))))) by RightForall
          thenHave(Set(!prem, forall(y, ((z === y) <=> (y === emptySet())))) |- exists(z, forall(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))))) by RightExists(
            z
          )
          thenHave(
            Set(!prem, exists(z, forall(y, ((z === y) <=> (y === emptySet()))))) |- exists(z, forall(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === emptySet()))))))
          ) by LeftExists
          thenHave(Set(!prem, existsOne(z, (z === emptySet()))) |- existsOne(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === emptySet()))))) by Restate
        }

      have(thesis) by Cut(emptyPrem, quantification)
    }

    val negRhs = thenHave(() |- Set(prem, existsOne(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === emptySet())))))) by Restate

    have(thesis) by Cut.withParameters(prem)(negRhs, positive)
  }

  /**
   * Function application --- denoted `f(x)`. The unique element `z` such that
   * `(x, z) \in f` if it exists and `f` is functional, [[emptySet]] otherwise.
   */
  val app =
    DEF(f, x) --> The(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === emptySet())))(functionApplicationUniqueness)

  /**
   * Surjective (function) --- a function `f: x \to y` is surjective iff it
   * maps to every `b \in y` from atleast one `a \in x`.
   *
   * `surjective(f, x, y) = f \in x \to y \land \forall b \in y. (\exists a \in x. f(a) = b)`
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ forall(b, in(b, y) ==> exists(a, in(pair(a, b), f)))

  /**
   * Alias for [[surjective]]
   */
  val onto = surjective

  /**
   * Injective (function) --- a function `f: x \to y` is injective iff it maps
   * to every `b \in y` from atmost one `a \in x`.
   *
   * `injective(f, x, y) = f \in x \to y \land \forall b \in y. (\exists a \in x. f(a) = b) ==> (\exists! a \in x. f(a) = b)`
   */
  val injective = DEF(f, x, y) --> functionFrom(f, x, y) /\ forall(b, in(b, y) ==> (exists(a, in(a, x) /\ in(pair(a, b), f)) ==> existsOne(a, in(a, x) /\ in(pair(a, b), f))))

  /**
   * Alias for [[injective]]
   */
  val oneone = injective

  /**
   * Bijective function --- a function `f: x \to y` is bijective iff it is
   * [[injective]] and [[surjective]].
   */
  val bijective = DEF(f, x, y) --> injective(f, x, y) /\ surjective(f, x, y)

  /**
   * Invertible Function --- a function from `x` to `y` is invertible iff it is
   * [[bijective]]. See also, [[inverseFunction]]
   */
  val invertibleFunction = DEF(f, x, y) --> bijective(f, x, y)

  /**
   * Inverse Function --- the inverse of a function `f: x \to y`, denoted
   * `f^-1`, is a function from `y` to `x` such that `\forall a \in x, b \in y.
   * f(f^-1(b)) = b /\ f^-1(f(b)) = b`.
   */
  val inverseFunctionOf = DEF(g, f, x, y) --> functionFrom(g, y, x) /\ functionFrom(f, x, y) /\ forall(a, (in(a, y) ==> (a === app(f, app(g, a)))) /\ (in(a, x) ==> (a === app(g, app(f, a)))))

  // val inverseFunctionExistsIfInvertible = makeTHM(
  //   () |- invertibleFunction(f, x, y) <=> exists(g, inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunctionIsUniqueIfItExists = makeTHM(
  //   exists(g, inverseFunctionOf(g, f, x, y)) |- existsOne(g, inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunctionUniqueness = makeTHM(
  //   () |- existsOne(g, invertibleFunction(f) ==> inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunction = DEF (f, x, y) --> The(g, invertibleFunction(f) ==> inverseFunctionOf(g, f, x, y))(inverseFunctionUniqueness)

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
   *    `restrictedFunction(f, x) = {(y, f(y)) | y ∈ x}`
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
  val reflexive = DEF(r, x) --> relationBetween(r, x, x) /\ forall(y, in(y, x) ==> in(pair(y, y), r))

  /**
   * Symmetric Relation --- `∀ x y. x R y ⇔ y R x`
   */
  val symmetric = DEF(r, x) --> relationBetween(r, x, x) /\ forall(y, forall(z, in(pair(y, z), r) <=> in(pair(z, y), r)))

  /**
   * Transitive Relation --- `∀ x y z. x R y ∧ y R z ⇒ x R z`
   */
  val transitive = DEF(r, x) --> relationBetween(r, x, x) /\ forall(w, forall(y, forall(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))))

  /**
   * Equivalence Relation --- A relation is an equivalence relation if it is
   * [[reflexive]], [[symmetric]], and [[transitive]].
   */
  val equivalence = DEF(r, x) --> reflexive(r, x) /\ symmetric(r, x) /\ transitive(r, x)

  /**
   * Anti-reflexive Relation --- `∀ x. ! x R x`
   */
  val antiReflexive = DEF(r, x) --> relationBetween(r, x, x) /\ forall(y, in(y, x) ==> !in(pair(y, y), r))

  /**
   * Irreflexive Relation --- Alias for [[antiReflexive]].
   */
  val irreflexive = antiReflexive

  /**
   * Anti-symmetric Relation --- `∀ x y. x R y ∧ y R x ⇒ y = x`
   */
  val antiSymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ forall(y, forall(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))

  /**
   * Asymmetric Relation --- `∀ x y. x R y ⇔ ! y R x`
   */
  val asymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ forall(y, forall(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))

  /**
   * Connected Relation --- `∀ x y. (x R y) ∨ (y R x) ∨ (y = x)`
   */
  val connected = DEF(r, x) --> relationBetween(r, x, x) /\ forall(y, forall(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z))))

  /**
   * Total Relation --- Alias for [[connected]].
   */
  val total = connected

  /**
   * Strongly Connected Relation ---
   *     `∀ x y z. y R x ∧ z R x ⇒ y R z ∨ z R y`
   */
  val stronglyConnected = DEF(r, x) --> relationBetween(r, x, x) /\ forall(y, forall(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r))))

  /**
   * Cantor theorem
   */

  // smaller needed lemmas
  // f from x to y => range f <= y
  // f from x to y => dom f = x
  // x <= y, y <= x |- x = y
  
  /**
   * Theorem ---  Subset reflexivity
   *
   * Every set is a [[subset]] of itself. In other words, the [[subset]]
   * predicate induces a [[reflexive]] [[relation]] on sets.
   */
  val subsetReflexivity = makeTHM(
    () |- subset(x, x)
  ) {
    val subdef = have(() |- subset(x, x) <=> forall(z, top())) by Rewrite(subsetAxiom of (y -> x))
    andThen(applySubst(closedFormulaUniversal of (VariableFormulaLabel("p") -> top())))

    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Symmetry of Equality and Subset
   *
   * [[equality]] implies a [[subset]] ordering, and [[subset]] ordering in both
   * directions implies [[equality]].
   */
  val subsetEqualitySymmetry = makeTHM(
    () |- (x === y) <=> (subset(x, y) /\ subset(y, x))
  ) {
    // we prove the implication directions separately

    // forward
    
    val fwd = have(() |- (x === y) ==> (subset(x, y) /\ subset(y, x))) subproof {
      have(() |- subset(x, x) /\ subset(x, x)) by Rewrite(subsetReflexivity)
      thenHave((x === y) |- (subset(x, y) /\ subset(y, x))) by RightSubstEq(List((x, y)), lambda(y, subset(x, y) /\ subset(y, x)))
      thenHave(thesis) by Restate
    }

    val bwd = have(() |- (subset(x, y) /\ subset(y, x)) ==> (x === y)) subproof {
      have(subset(x, y) |- forall(z, in(z, x) ==> in(z, y))) by Tautology.from(subsetAxiom)
      val sxy = thenHave(subset(x, y) |- in(z, x) ==> in(z, y)) by InstantiateForall(z)

      have(subset(y, x) |- forall(z, in(z, y) ==> in(z, x))) by Tautology.from(subsetAxiom of (x -> y, y -> x))
      val syx = thenHave(subset(y, x) |- in(z, y) ==> in(z, x)) by InstantiateForall(z)

      have(Set(subset(x, y), subset(y, x)) |- in(z, y) <=> in(z, x)) by RightIff(sxy, syx)
      thenHave(Set(subset(x, y) /\ subset(y, x)) |- in(z, y) <=> in(z, x)) by Restate
      val ssxy = thenHave(subset(x, y) /\ subset(y, x) |- forall(z, in(z, y) <=> in(z, x))) by RightForall

      val ext = have(() |- (x === y) <=> (forall(z, in(z, y) <=> in(z, x)))) by Rewrite(extensionalityAxiom)

      have(subset(x, y) /\ subset(y, x) |- forall(z, in(z, y) <=> in(z, x)) /\ ((x === y) <=> (forall(z, in(z, y) <=> in(z, x))))) by RightAnd(ssxy, ext)
      thenHave(subset(x, y) /\ subset(y, x) |- (x === y)) by Tautology
      thenHave(thesis) by Restate
    }

    have(thesis) by RightAnd(fwd, bwd)
  }

  val functionalOverImpliesDomain = makeTHM(
    functionalOver(f, x) |- (relationDomain(f) === x)
  ) {
    have(thesis) by Tautology.from(functionalOver.definition)
  }

  val functionFromImpliesDomainEq = makeTHM(
    functionFrom(f, x, y) |- (relationDomain(f) === x)
  ) {
    have(() |- forall(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(() |- in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(thesis) by Tautology.from(functionFrom.definition, funSetDef, functionalOver.definition)
  }

  val functionImpliesRangeSubsetOfCodomain = makeTHM(
    functionFrom(f, x, y) |- subset(relationRange(f), y)
  ) {
    have(() |- forall(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(() |- in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(functionFrom(f, x, y) |- forall(z, in(z, f) ==> in(z, cartesianProduct(x, y)))) by Tautology.from(functionFrom.definition, funSetDef, powerAxiom of (x -> f, y -> cartesianProduct(x, y)), subsetAxiom of (x -> f, y -> cartesianProduct(x, y)))
    thenHave(functionFrom(f, x, y) |- in(pair(a, t), f) ==> in(pair(a, t), cartesianProduct(x, y))) by InstantiateForall(pair(a, t))
    thenHave(Set(functionFrom(f, x, y), in(pair(a, t), f)) |- in(pair(a, t), cartesianProduct(x, y))) by Restate
    andThen(applySubst(pairInCartesianProduct of (b -> t)))
    thenHave(Set(functionFrom(f, x, y), in(pair(a, t), f)) |- in(t, y)) by Weakening
    val funFromty = thenHave(Set(functionFrom(f, x, y), exists(a, in(pair(a, t), f))) |- in(t, y)) by LeftExists

    have(() |- forall(t, in(t, relationRange(f)) <=> (exists(a, in(pair(a, t), f))))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    thenHave(() |- in(t, relationRange(f)) <=> (exists(a, in(pair(a, t), f)))) by InstantiateForall(t)
    val ranat = thenHave(in(t, relationRange(f)) |- exists(a, in(pair(a, t), f))) by Weakening

    have(Set(functionFrom(f, x, y), in(t, relationRange(f))) |- in(t, y)) by Cut(ranat, funFromty)
    thenHave(Set(functionFrom(f, x, y)) |- in(t, relationRange(f)) ==> in(t, y)) by Restate
    thenHave(Set(functionFrom(f, x, y)) |- forall(t, in(t, relationRange(f)) ==> in(t, y))) by RightForall
    andThen(applySubst(subsetAxiom of (x -> relationRange(f))))
  }

  val inRangeImpliesPullbackExists = makeTHM(
    functional(f) /\ in(z, relationRange(f)) |- exists(t, in(t, relationDomain(f)) /\ (app(f, t) === z))
  ) {
    val appIff = have(() |- (z === app(f, t)) <=> ((functional(f) /\ in(t, relationDomain(f))) ==> in(pair(t, z), f)) /\ ((!functional(f) \/ !in(t, relationDomain(f))) ==> (z === emptySet()))) by InstantiateForall(z)(app.definition of (x -> t))

    have(() |- forall(t, in(t, relationRange(f)) <=> exists(a, in(pair(a, t), f)))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    thenHave(() |- in(z, relationRange(f)) <=> exists(a, in(pair(a, z), f))) by InstantiateForall(z)
    val elementInDomainExists = thenHave(in(z, relationRange(f)) |- exists(t, in(pair(t, z), f))) by Weakening

    val toApp = have(Set(functional(f), in(t, relationDomain(f)), in(pair(t, z), f)) |- ((functional(f) /\ in(t, relationDomain(f))) ==> in(pair(t, z), f)) /\ ((!functional(f) \/ !in(t, relationDomain(f))) ==> (z === emptySet()))) by Restate
    val zAppdom = have(Set(functional(f), in(t, relationDomain(f)), in(pair(t, z), f)) |- (z === app(f, t))) by Tautology.from(toApp, appIff)

    val pairInDomain = have(in(pair(t, z), f) |- in(t, relationDomain(f))) subproof {
      have(() |- forall(t, in(t, relationDomain(f)) <=> exists(a, in(pair(t, a), f)))) by InstantiateForall(relationDomain(f))(relationDomain.definition of (r -> f))
      val domDef = thenHave(() |- in(t, relationDomain(f)) <=> exists(a, in(pair(t, a), f))) by InstantiateForall(t)

      have(in(pair(t, z), f) |- in(pair(t, z), f)) by Hypothesis
      val pairEx = thenHave(in(pair(t, z), f) |- exists(a, in(pair(t, a), f))) by RightExists(z)

      have(thesis) by Tautology.from(domDef, pairEx)
    }

    val zApp2 = have(Set(functional(f), in(pair(t, z), f)) |- (z === app(f, t))) by Cut(pairInDomain, zAppdom)
    have(Set(functional(f), in(pair(t, z), f)) |- in(t, relationDomain(f)) /\ (z === app(f, t))) by RightAnd(pairInDomain, zApp2)
    thenHave(Set(functional(f), in(pair(t, z), f)) |- exists(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by RightExists(t)
    val zAppIfExists = thenHave(Set(functional(f), exists(t, in(pair(t, z), f))) |- exists(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by LeftExists

    have(Set(functional(f), in(z, relationRange(f))) |- exists(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by Cut(elementInDomainExists, zAppIfExists)
    thenHave(thesis) by Restate
  }

  val surjectiveImpliesRangeIsCodomain = makeTHM(
    surjective(f, x, y) |- (y === relationRange(f))
  ) {
    have(surjective(f, x, y) |- forall(b, in(b, y) ==> exists(a, in(pair(a, b), f)))) by Tautology.from(surjective.definition)
    val surjDef = thenHave(surjective(f, x, y) |- in(b, y) ==> exists(a, in(pair(a, b), f))) by InstantiateForall(b)
    have(() |- forall(t, in(t, relationRange(f)) <=> (exists(a, in(pair(a, t), f))))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    val rangeDef = thenHave(() |- in(b, relationRange(f)) <=> (exists(a, in(pair(a, b), f)))) by InstantiateForall(b)

    have(surjective(f, x, y) |- in(b, y) ==> in(b, relationRange(f))) by Tautology.from(surjDef, rangeDef)
    thenHave(surjective(f, x, y) |- forall(b, in(b, y) ==> in(b, relationRange(f)))) by RightForall
    val surjsub = andThen(applySubst(subsetAxiom of (x -> y, y -> relationRange(f))))

    have(Set(surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, relationRange(f)) /\ subset(relationRange(f), y)) by RightAnd(surjsub, functionImpliesRangeSubsetOfCodomain)
    val funceq = andThen(applySubst(subsetEqualitySymmetry of (x -> y, y -> relationRange(f))))

    val surjfunc = have(surjective(f, x, y) |- functionFrom(f, x, y)) by Tautology.from(surjective.definition)

    have(thesis) by Cut(surjfunc, funceq)
  }

  val cantorTheorem = makeTHM(
    surjective(f, x, powerSet(x)) |- ()
  ) {
    // define y = {z \in x | ! z \in f(z)}
    val ydef = forall(t, in(t, y) <=> (in(t, x) /\ !in(t, app(f, t))))

    // y \subseteq x
    // y \in P(x)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(t, y) <=> (in(t, x) /\ !in(t, app(f, t)))) by InstantiateForall(t)
    thenHave(ydef |- in(t, y) ==> in(t, x)) by Weakening
    thenHave(ydef |- forall(t, in(t, y) ==> in(t, x))) by RightForall
    andThen(applySubst(subsetAxiom of (x -> y, y -> x)))
    andThen(applySubst(powerAxiom of (x -> y, y -> x)))
    val yInPower = thenHave(ydef |- in(y, powerSet(x))) by Restate

    // y \in range(f)
    have(surjective(f, x, powerSet(x)) |- (powerSet(x) === relationRange(f))) by Rewrite(surjectiveImpliesRangeIsCodomain of (y -> powerSet(x)))
    andThen(applySubst(extensionalityAxiom of (x -> powerSet(x), y -> relationRange(f))))
    val surjRange = thenHave(surjective(f, x, powerSet(x)) |- in(y, powerSet(x)) <=> in(y, relationRange(f))) by InstantiateForall(y)
    val yInRange = have(Set(ydef, surjective(f, x, powerSet(x))) |- in(y, relationRange(f))) by Tautology.from(yInPower, surjRange)

    // \exists z. z \in x /\ f(z) = y
    val funToExists = have(Set(functional(f), in(y, relationRange(f))) |- exists(z, in(z, relationDomain(f)) /\ (app(f, z) === y))) by Rewrite(inRangeImpliesPullbackExists of (z -> y))
    val funFromImpliesFun = have(functionFrom(f, x, powerSet(x)) |- functional(f)) by Rewrite(functionFromImpliesFunctional of (y -> powerSet(x)))
    val surjToFunFrom = have(surjective(f, x, powerSet(x)) |- functionFrom(f, x, powerSet(x))) by Tautology.from(surjective.definition of (y -> powerSet(x)))
    val funFromToExists = have(Set(functionFrom(f, x, powerSet(x)), in(y, relationRange(f))) |- exists(z, in(z, relationDomain(f)) /\ (app(f, z) === y))) by Cut(funFromImpliesFun, funToExists)
    val surjToExists = have(Set(surjective(f, x, powerSet(x)), in(y, relationRange(f))) |- exists(z, in(z, relationDomain(f)) /\ (app(f, z) === y))) by Cut(surjToFunFrom, funFromToExists)
    val existsZdom = have(Set(ydef, surjective(f, x, powerSet(x))) |- exists(z, in(z, relationDomain(f)) /\ (app(f, z) === y))) by Cut(yInRange, surjToExists)
    val xeqdom = thenHave(Set(ydef, surjective(f, x, powerSet(x)), (relationDomain(f) === x)) |- exists(z, in(z, x) /\ (app(f, z) === y))) by RightSubstEq(List((x, relationDomain(f))), lambda(x, exists(z, in(z, x) /\ (app(f, z) === y))))
    val funtox = have(Set(ydef, surjective(f, x, powerSet(x)), functionFrom(f, x, powerSet(x))) |- exists(z, in(z, x) /\ (app(f, z) === y))) by Cut(functionFromImpliesDomainEq of (y -> powerSet(x)), xeqdom)
    val existsZ = have(Set(ydef, surjective(f, x, powerSet(x))) |- exists(z, in(z, x) /\ (app(f, z) === y))) by Cut(surjToFunFrom, funtox)

    // z \in Y <=> z \in x /\ ! z \in f(z)
    // y = f(z) so z \in f(z) <=> ! z \in f(z) 
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by InstantiateForall(z)
    thenHave(Set(ydef, in(z, x), (app(f, z) === y)) |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by Weakening
    thenHave(Set(ydef, in(z, x), (app(f, z) === y)) |- in(z, app(f, z)) <=> (in(z, x) /\ !in(z, app(f, z)))) by RightSubstEq(List((y, app(f, z))), lambda(y, in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))))
    thenHave(Set(ydef, in(z, x) /\ (app(f, z) === y)) |- ()) by Tautology
    val existsToContra = thenHave(Set(ydef, exists(z, in(z, x) /\ (app(f, z) === y))) |- ()) by LeftExists

    have(Set(ydef, surjective(f, x, powerSet(x))) |- ()) by Cut(existsZ, existsToContra)
    val yToContra = thenHave(Set(exists(y, ydef), surjective(f, x, powerSet(x))) |- ()) by LeftExists
    val yexists = have(() |- exists(y, ydef)) by Rewrite(comprehensionSchema of (z -> x, sPhi -> lambda(Seq(t, z), !in(t, app(f, t)))))

    have(thesis) by Cut(yexists, yToContra)
  }
  show
}
