package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
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
  val russelsParadox = Theorem(
    ∃(x, ∀(y, !in(y, y) <=> in(y, x))) |- ()
  ) {
    val contra = !in(x, x) <=> in(x, x)

    have(contra |- ()) by Restate
    thenHave(∀(y, !in(y, y) <=> in(y, x)) |- ()) by LeftForall
    thenHave(∃(x, ∀(y, !in(y, y) <=> in(y, x))) |- ()) by LeftExists
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
   * have(∃(z, ∀(t, in(t, z) ⇔ myProperty(t))) ⊢ ∃!(z, ∀(t, in(t, z) ⇔ myProperty(t)))) by InstPredSchema(Map(schemPred -> (t, myProperty(t))))`
   * }}}
   *
   * Instantiation will fail if `myProperty(t)` contains `z` as a free variable.
   */
  val uniqueByExtension = Theorem(
    ∃(z, ∀(t, in(t, z) <=> schemPred(t))) |- ∃!(z, ∀(t, in(t, z) <=> schemPred(t)))
  ) {
    def prop(z: Term) = in(t, z) <=> schemPred(t)
    def fprop(z: Term) = ∀(t, prop(z))

    // forward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    thenHave(fprop(z) /\ (z === a) |- fprop(z)) by Weakening
    thenHave((fprop(z) /\ (z === a), (z === a)) |- fprop(a)) by RightSubstEq(List((z, a)), lambda(Seq(z), fprop(z)))
    val forward = thenHave(fprop(z) |- (z === a) ==> fprop(a)) by Restate

    // backward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    val instLhs = thenHave(fprop(z) |- prop(z)) by InstantiateForall(t)
    val instRhs = thenHave(fprop(a) |- prop(a)) by InstFunSchema(Map(z -> a))

    have((fprop(z), fprop(a)) |- prop(z) /\ prop(a)) by RightAnd(instLhs, instRhs)
    thenHave(fprop(z) /\ fprop(a) |- in(t, a) <=> in(t, z)) by Tautology
    val extLhs = thenHave(fprop(z) /\ fprop(a) |- ∀(t, in(t, a) <=> in(t, z))) by RightForall
    val extRhs = have(∀(t, in(t, a) <=> in(t, z)) <=> (a === z)) by InstFunSchema(Map(x -> a, y -> z))(extensionalityAxiom)

    have(fprop(z) /\ fprop(a) |- (∀(t, in(t, a) <=> in(t, z)) <=> (a === z)) /\ ∀(t, in(t, a) <=> in(t, z))) by RightAnd(extLhs, extRhs)
    thenHave(fprop(z) /\ fprop(a) |- (a === z)) by Tautology
    val backward = thenHave(fprop(z) |- fprop(a) ==> (a === z)) by Restate

    have(fprop(z) |- fprop(a) <=> (a === z)) by RightIff(forward, backward)
    thenHave(fprop(z) |- ∀(a, fprop(a) <=> (a === z))) by RightForall
    thenHave(fprop(z) |- ∃(z, ∀(a, fprop(a) <=> (a === z)))) by RightExists
    thenHave(∃(z, fprop(z)) |- ∃(z, ∀(a, fprop(a) <=> (a === z)))) by LeftExists
    thenHave(∃(z, fprop(z)) |- ∃!(z, fprop(z))) by RightExistsOne
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
   * Theorem --- a set is an element of `x ∪ y` iff it is an element of `x` or `y`
   */
  val setUnionMembership = Theorem(
    in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))
  ) {
    have(∀(z, (z === setUnion(x, y)) <=> (z === union(unorderedPair(x, y))))) by Restate.from(setUnion.definition)
    thenHave((setUnion(x, y) === setUnion(x, y)) <=> (setUnion(x, y) === union(unorderedPair(x, y)))) by InstantiateForall(setUnion(x, y))
    val unionDef = thenHave((setUnion(x, y) === union(unorderedPair(x, y)))) by Restate

    val upairax = have(in(a, unorderedPair(x, y)) <=> ((a === x) \/ (a === y))) by Restate.from(pairAxiom of (z -> a))

    val ta = have(in(z, union(unorderedPair(x, y))) <=> ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate.from(unionAxiom of (x -> unorderedPair(x, y)))

    have(thesis) subproof {
      // the proof proceeds by showing that the existence criterion reduces to the RHS of the iff in the thesis

      val fwd = have(∃(a, in(z, a) /\ in(a, unorderedPair(x, y))) ==> (in(z, x) \/ in(z, y))) subproof {
        have((in(z, a), a === x) |- in(z, a)) by Hypothesis
        val tax = thenHave((in(z, a), a === x) |- in(z, x)) by RightSubstEq(List((a, x)), lambda(a, in(z, a)))

        have((in(z, a), a === y) |- in(z, a)) by Hypothesis
        val tay = thenHave((in(z, a), a === y) |- in(z, y)) by RightSubstEq(List((a, y)), lambda(a, in(z, a)))

        have((in(z, a), (a === x) \/ (a === y)) |- (in(z, x), in(z, y))) by LeftOr(tax, tay)
        andThen(Simplify.once(true, upairax))
        thenHave((in(z, a) /\ in(a, unorderedPair(x, y))) |- (in(z, x), in(z, y))) by Restate
        thenHave(∃(a, in(z, a) /\ in(a, unorderedPair(x, y))) |- (in(z, x), in(z, y))) by LeftExists
        thenHave(thesis) by Restate
      }

      val bwd = have(((in(z, x) \/ in(z, y)) ==> ∃(a, in(z, a) /\ in(a, unorderedPair(x, y))))) subproof {
        have((in(z, x), (a === x)) |- in(z, x)) by Hypothesis
        thenHave((in(z, x), (a === x)) |- in(z, a)) by RightSubstEq(List((a, x)), lambda(a, in(z, a)))
        thenHave((in(z, x), (a === x)) |- in(z, a) /\ ((a === x) \/ (a === y))) by Tautology
        andThen(applySubst(upairax, false))
        thenHave((in(z, x), (a === x)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by RightExists
        thenHave((in(z, x), (x === x)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by InstFunSchema(Map(a -> x))
        val tax = thenHave((in(z, x)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate

        have((in(z, y), (a === y)) |- in(z, y)) by Hypothesis
        thenHave((in(z, y), (a === y)) |- in(z, a)) by RightSubstEq(List((a, y)), lambda(a, in(z, a)))
        thenHave((in(z, y), (a === y)) |- in(z, a) /\ ((a === x) \/ (a === y))) by Tautology
        andThen(applySubst(upairax, false))
        thenHave((in(z, y), (a === y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by RightExists
        thenHave((in(z, y), (y === y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by InstFunSchema(Map(a -> y))
        val tay = thenHave((in(z, y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate

        have((in(z, x) \/ in(z, y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by LeftOr(tax, tay)
        thenHave(thesis) by Restate
      }

      val existsSubst = have(∃(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> (in(z, x) \/ in(z, y))) by RightIff(fwd, bwd)

      have(in(z, union(unorderedPair(x, y))) <=> ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate.from(ta)
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
  val inductive = DEF(x) --> in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x))

  /**
   * Theorem --- There exists an inductive set.
   *
   *    `∃ x. inductive(x)`
   *
   * Equivalent to the Axiom of Infinity ([[infinityAxiom]]). The proof shows
   * that the two forms are equivalent by folding the definitions of
   * [[successor]] and [[inductive]].
   */
  val inductiveSetExists = Theorem(
    ∃(x, inductive(x))
  ) {
    val form = formulaVariable

    have(∀(x, (x === successor(y)) <=> (x === union(unorderedPair(y, unorderedPair(y, y)))))) by InstFunSchema(Map(x -> y))(successor.definition)
    thenHave(((successor(y) === successor(y)) <=> (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))))) by InstantiateForall(successor(y))
    val succDef = thenHave((successor(y) === union(unorderedPair(y, unorderedPair(y, y))))) by Restate
    val inductDef = have(inductive(x) <=> in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x))) by Restate.from(inductive.definition)

    have((in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Restate
    val succEq = thenHave(
      (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(successor(y), x))
    ) by RightSubstEq(
      List((successor(y), union(unorderedPair(y, unorderedPair(y, y))))),
      lambda(z, (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(z, x)))
    )
    val iffinst = have((in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(successor(y), x))) by Cut(succDef, succEq)

    val iffquant = {
      have((in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (in(y, x) ==> in(successor(y), x))) by Weakening(iffinst)
      thenHave(∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (in(y, x) ==> in(successor(y), x))) by LeftForall
      thenHave(∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- ∀(y, in(y, x) ==> in(successor(y), x))) by RightForall
      val lhs = thenHave(∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) ==> ∀(y, in(y, x) ==> in(successor(y), x))) by Restate

      have((in(y, x) ==> in(successor(y), x)) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Weakening(iffinst)
      thenHave(∀(y, in(y, x) ==> in(successor(y), x)) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by LeftForall
      thenHave(∀(y, in(y, x) ==> in(successor(y), x)) |- ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by RightForall
      val rhs = thenHave(∀(y, in(y, x) ==> in(successor(y), x)) ==> ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Restate

      have(∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, in(y, x) ==> in(successor(y), x))) by RightIff(lhs, rhs)
    }

    have(
      in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- in(∅, x) /\ ∀(
        y,
        in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)
      )
    ) by Hypothesis
    thenHave(
      (
        ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, in(y, x) ==> in(successor(y), x)),
        in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
      ) |- in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x))
    ) by RightSubstIff(
      List((∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)), ∀(y, in(y, x) ==> in(successor(y), x)))),
      lambda(form, in(∅, x) /\ form)
    )
    val substituted = thenHave(
      (
        inductive(x) <=> in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x)),
        ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, in(y, x) ==> in(successor(y), x)),
        in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
      ) |- inductive(x)
    ) by RightSubstIff(List((inductive(x), in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x)))), lambda(form, form))
    val cut1 = have(
      (
        ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, in(y, x) ==> in(successor(y), x)),
        in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
      ) |- inductive(x)
    ) by Cut(inductDef, substituted)
    val cut2 = have((in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) |- inductive(x)) by Cut(iffquant, cut1)

    thenHave((in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) |- ∃(x, inductive(x))) by RightExists
    val rhs = thenHave((∃(x, in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)))) |- ∃(x, inductive(x))) by LeftExists

    have(∃(x, inductive(x))) by Cut(infinityAxiom, rhs)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Properties about the empty set and power sets
   */

  /**
   * Theorem --- If a set has an element, then it is not the empty set.
   *
   *    `(∃ y.) y ∈ x ⊢ ! x = ∅`
   */
  val setWithElementNonEmpty = Theorem(
    in(y, x) |- !(x === ∅)
  ) {
    have(!in(y, ∅)) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    thenHave(in(y, ∅) |- ()) by Restate
    thenHave((in(y, x), (x === ∅)) |- ()) by LeftSubstEq(List((x, ∅)), lambda(Seq(x), in(y, x)))
    thenHave(in(y, x) |- !(x === ∅)) by Restate
  }

  /**
   * Theorem --- A set containing no elements is equivalent to the empty set.
   *
   *    `∀ y. ! y ∈ x ⊢ x = ∅`
   *
   * Converse of the empty set axiom ([[emptySetAxiom]]).
   */
  val setWithNoElementsIsEmpty = Theorem(
    ∀(y, !in(y, x)) |- (x === ∅)
  ) {
    have(!in(y, ∅)) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    thenHave(() |- (!in(y, ∅), in(y, x))) by Weakening
    val lhs = thenHave(in(y, ∅) ==> in(y, x)) by Restate

    have(!in(y, x) |- !in(y, x)) by Hypothesis
    thenHave(!in(y, x) |- (!in(y, x), in(y, ∅))) by Weakening
    val rhs = thenHave(!in(y, x) |- in(y, x) ==> in(y, ∅)) by Restate

    have(!in(y, x) |- in(y, x) <=> in(y, ∅)) by RightIff(lhs, rhs)
    thenHave(∀(y, !in(y, x)) |- in(y, x) <=> in(y, ∅)) by LeftForall
    val exLhs = thenHave(∀(y, !in(y, x)) |- ∀(y, in(y, x) <=> in(y, ∅))) by RightForall

    have(∀(z, in(z, x) <=> in(z, ∅)) <=> (x === ∅)) by InstFunSchema(Map(x -> x, y -> ∅))(extensionalityAxiom)
    val exRhs = thenHave(∀(y, in(y, x) <=> in(y, ∅)) <=> (x === ∅)) by Restate

    have(∀(y, !in(y, x)) |- (∀(y, in(y, x) <=> in(y, ∅)) <=> (x === ∅)) /\ ∀(y, in(y, x) <=> in(y, ∅))) by RightAnd(exLhs, exRhs)
    thenHave(∀(y, !in(y, x)) |- (x === ∅)) by Tautology
  }

  /**
   * Theorem --- The empty set is a subset of every set.
   *
   *    `(∀ x.) x ⊆ ∅`
   */
  val emptySetIsASubset = Theorem(
    subset(∅, x)
  ) {
    val lhs = have(subset(∅, x) <=> ∀(z, in(z, ∅) ==> in(z, x))) by InstFunSchema(Map(x -> ∅, y -> x))(subsetAxiom)

    have(!in(y, ∅)) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    thenHave(in(y, ∅) ==> in(y, x)) by Weakening
    val rhs = thenHave(∀(y, in(y, ∅) ==> in(y, x))) by RightForall

    have((subset(∅, x) <=> ∀(z, in(z, ∅) ==> in(z, x))) /\ ∀(y, in(y, ∅) ==> in(y, x))) by RightAnd(lhs, rhs)
    thenHave((subset(∅, x) <=> ∀(z, in(z, ∅) ==> in(z, x))) /\ ∀(z, in(z, ∅) ==> in(z, x))) by Restate
    thenHave(subset(∅, x)) by Tautology
  }

  /**
   * Theorem --- If a set is a subset of the empty set, it is empty.
   *
   *    `x ⊆ ∅ <=> a = ∅`
   */
  val emptySetIsItsOwnOnlySubset = Theorem(
    subset(x, emptySet()) <=> (x === emptySet())
  ) {
    val fwd = have(subset(x, emptySet()) |- (x === emptySet())) subproof {
      have(subset(x, emptySet()) |- forall(z, in(z, x) ==> in(z, emptySet()))) by Weakening(subsetAxiom of y -> emptySet())
      thenHave(subset(x, emptySet()) |- in(z, x) ==> in(z, emptySet())) by InstantiateForall(z)
      have(subset(x, emptySet()) |- !in(z, x)) by Tautology.from(lastStep, emptySetAxiom of x -> z)
      thenHave(subset(x, emptySet()) |- forall(z, !in(z, x))) by RightForall

      have(thesis) by Cut(lastStep, setWithNoElementsIsEmpty)
    }

    val bwd = have((x === emptySet()) |- subset(x, emptySet())) subproof {
      have(subset(emptySet(), emptySet())) by Restate.from(emptySetIsASubset of x -> emptySet())
      thenHave(thesis) by Substitution.apply2(true, x === emptySet())
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

  /**
   * Theorem --- A power set is never empty.
   *
   *    `! P(x) = ∅`
   */
  val powerSetNonEmpty = Theorem(
    !(powerSet(x) === ∅)
  ) {
    // strategy
    //      prove power set contains empty set
    //      since it has an element, it is not empty itself

    val lhs = have(in(∅, powerSet(x)) <=> subset(∅, x)) by InstFunSchema(Map(x -> ∅, y -> x))(powerAxiom)

    have((in(∅, powerSet(x)) <=> subset(∅, x)) /\ subset(∅, x)) by RightAnd(lhs, emptySetIsASubset)
    val emptyinPower = thenHave(in(∅, powerSet(x))) by Tautology
    val nonEmpty = have(in(∅, powerSet(x)) |- !(powerSet(x) === ∅)) by InstFunSchema(Map(y -> ∅, x -> powerSet(x)))(setWithElementNonEmpty)

    have(!(powerSet(x) === ∅)) by Cut(emptyinPower, nonEmpty)
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
  val firstElemInPair = Theorem(
    in(x, unorderedPair(x, y))
  ) {
    val lhs = have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstFunSchema(Map(x -> x, y -> y, z -> z))(ax"pairAxiom")
    have((z === x) |- (z === x)) by Hypothesis
    val rhs = thenHave((z === x) |- (z === x) \/ (z === y)) by Restate
    val factset = have((z === x) |- (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    thenHave((z === x) |- in(z, unorderedPair(x, y))) by Tautology
    thenHave((x === x) |- in(x, unorderedPair(x, y))) by InstFunSchema(Map(z -> x))
    thenHave(in(x, unorderedPair(x, y))) by LeftRefl
  }

  /**
   * Theorem --- Second Element in Pair
   *
   *    `y ∈ {x, y}`
   *
   * Unfolds the definition of [[unorderedPair]]. Easier to use in theorems than
   * the complete definition.
   */
  val secondElemInPair = Theorem(
    in(y, unorderedPair(x, y))
  ) {
    val lhs = have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstFunSchema(Map(x -> x, y -> y, z -> z))(ax"pairAxiom")
    have((z === y) |- (z === y)) by Hypothesis
    val rhs = thenHave((z === y) |- (z === x) \/ (z === y)) by Restate
    val factset = have((z === y) |- (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    thenHave((z === y) |- in(z, unorderedPair(x, y))) by Tautology
    thenHave((y === y) |- in(y, unorderedPair(x, y))) by InstFunSchema(Map(z -> y))
    thenHave(in(y, unorderedPair(x, y))) by LeftRefl
  }

  /**
   * Theorem --- If a set belongs to a [[singleton]], it must be the single element.
   *
   *    `y ∈ {x} <=> y = x`
   */
  val singletonHasNoExtraElements = Theorem(
    in(y, singleton(x)) <=> (x === y)
  ) {
    // specialization of the pair axiom to a singleton

    have(in(y, unorderedPair(x, x)) <=> (x === y) \/ (x === y)) by InstFunSchema(Map(x -> x, y -> x, z -> y))(pairAxiom)
    thenHave(in(y, singleton(x)) <=> (x === y)) by Restate
  }

  /**
   * Theorem --- The [[unorderedPair]] is indeed, unordered.
   *
   *    `{x, y} = {y, x}`
   */
  val unorderedPairSymmetry = Theorem(unorderedPair(x, y) === unorderedPair(y, x)) {
    have((y === z) \/ (x === z) <=> in(z, unorderedPair(y, x))) by InstFunSchema(Map(x -> y, y -> x))(pairAxiom)
    andThen(applySubst.apply(pairAxiom))
    val part1 = thenHave(∀(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))) by RightForall
    val part2 = have(∀(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x))) by InstFunSchema(
      Map(x -> unorderedPair(x, y), y -> unorderedPair(y, x))
    )(extensionalityAxiom)
    val fin = have(applySubst(∀(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x)))(part1))
    have(thesis) by Cut(part2, fin)
  }

  val unorderedPairDeconstruction = Theorem("unorderedPair('a, 'b) = unorderedPair('c, 'd) ⊢ 'a = 'c ∧ 'b = 'd ∨ 'a = 'd ∧ 'b = 'c") {
    val s1 = have(applySubst(unorderedPair(a, b) === unorderedPair(c, d))(pairAxiom of (x -> a, y -> b)))
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
  val unionOfSingletonIsTheOriginalSet = Theorem((union(singleton(x)) === x)) {
    val X = singleton(x)
    val forward = have((in(z, x) ==> in(z, union(X)))) subproof {
      have(in(z, x) |- in(z, x) /\ in(x, X)) by Tautology.from(pairAxiom of (y -> x, z -> x))
      val step2 = thenHave(in(z, x) |- ∃(y, in(z, y) /\ in(y, X))) by RightExists
      have(thesis) by Tautology.from(step2, unionAxiom of (x -> X))
    }

    val backward = have(in(z, union(X)) ==> in(z, x)) subproof {
      have(in(z, y) |- in(z, y)) by Restate
      val step2 = thenHave((y === x, in(z, y)) |- in(z, x)) by Substitution
      have(in(z, y) /\ in(y, X) |- in(z, x)) by Tautology.from(pairAxiom of (y -> x, z -> y), step2)
      val step4 = thenHave(∃(y, in(z, y) /\ in(y, X)) |- in(z, x)) by LeftExists
      have(in(z, union(X)) ==> in(z, x)) by Tautology.from(unionAxiom of (x -> X), step4)
    }

    have(in(z, union(X)) <=> in(z, x)) by RightIff(forward, backward)
    thenHave(∀(z, in(z, union(X)) <=> in(z, x))) by RightForall
    andThen(applySubst(extensionalityAxiom of (x -> union(X), y -> x)))
  }

  /**
   * Theorem --- Two [[unorderedPair]]s are equal iff their elements are equal pairwise.
   *
   *    `{a, b} = {c, d} <=> ( (a = c ∧ b = d) ∨ (a = d ∧ b = c) )`
   */
  val unorderedPairExtensionality = Theorem(
    (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))
  ) {
    // forward direction
    //      up ab = up cd |- a = c and b = d OR a = d and b = c
    val fwd = have((unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by Restate.from(unorderedPairDeconstruction)

    // backward direction
    //      a = c and b = d => up ab = up cd (and the other case)
    have(unorderedPair(a, b) === unorderedPair(a, b)) by RightRefl
    thenHave((a === c, b === d) |- unorderedPair(a, b) === unorderedPair(c, d)) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(x, y)))
    val lhs = thenHave(Set((a === c) /\ (b === d)) |- unorderedPair(a, b) === unorderedPair(c, d)) by Restate

    have(unorderedPair(a, b) === unorderedPair(b, a)) by InstFunSchema(Map(x -> a, y -> b))(unorderedPairSymmetry)
    thenHave((a === d, b === c) |- (unorderedPair(a, b) === unorderedPair(c, d))) by RightSubstEq(List((a, d), (b, c)), lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(y, x)))
    val rhs = thenHave(Set((a === d) /\ (b === c)) |- (unorderedPair(a, b) === unorderedPair(c, d))) by Restate

    have((((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) |- (unorderedPair(a, b) === unorderedPair(c, d))) by LeftOr(lhs, rhs)
    val bwd = thenHave((((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) ==> (unorderedPair(a, b) === unorderedPair(c, d))) by Restate

    have((unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by RightIff(fwd, bwd)
  }

  /**
   * Theorem --- A singleton set is never empty.
   *
   *    `! {x} = ∅`
   */
  val singletonNonEmpty = Theorem(
    !(singleton(x) === ∅)
  ) {
    val reflLhs = have(in(x, singleton(x)) <=> (x === x)) by InstFunSchema(Map(y -> x))(singletonHasNoExtraElements)

    val reflRhs = have((x === x)) by RightRefl
    have((x === x) /\ (in(x, singleton(x)) <=> (x === x))) by RightAnd(reflLhs, reflRhs)
    val lhs = thenHave(in(x, singleton(x))) by Tautology

    val rhs = have(in(x, singleton(x)) |- !(singleton(x) === ∅)) by InstFunSchema(Map(y -> x, x -> singleton(x)))(setWithElementNonEmpty)

    have(!(singleton(x) === ∅)) by Cut(lhs, rhs)
  }

  /**
   * Theorem --- Two singletons are equal iff their elements are equal
   *
   *    `{x} = {y} <=> x = y`
   */
  val singletonExtensionality = Theorem(
    (singleton(x) === singleton(y)) <=> (x === y)
  ) {
    // forward direction
    // {x} === {y} |- x === y
    have(∀(z, in(z, singleton(x)) <=> in(z, singleton(y))) <=> (singleton(x) === singleton(y))) by InstFunSchema(Map(x -> singleton(x), y -> singleton(y)))(extensionalityAxiom)
    thenHave((singleton(x) === singleton(y)) |- ∀(z, in(z, singleton(x)) <=> in(z, singleton(y)))) by Tautology
    val singiff = thenHave((singleton(x) === singleton(y)) |- in(z, singleton(x)) <=> in(z, singleton(y))) by InstantiateForall(z)

    val singX = have(in(z, singleton(x)) <=> (z === x)) by InstFunSchema(Map(y -> z))(singletonHasNoExtraElements)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(x)) <=> in(z, singleton(y))) /\ (in(z, singleton(x)) <=> (z === x))) by RightAnd(singiff, singX)
    val yToX = thenHave((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x))) by Tautology

    val singY = have(in(z, singleton(y)) <=> (z === y)) by InstFunSchema(Map(x -> y))(singX)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x)) /\ (in(z, singleton(y)) <=> (z === y))) by RightAnd(yToX, singY)
    thenHave((singleton(x) === singleton(y)) |- ((z === x) <=> (z === y))) by Tautology
    thenHave((singleton(x) === singleton(y)) |- ((x === x) <=> (x === y))) by InstFunSchema(Map(z -> x))

    thenHave((singleton(x) === singleton(y)) |- (x === y)) by Restate
    val fwd = thenHave((singleton(x) === singleton(y)) ==> (x === y)) by Tautology

    // backward direction
    //  x === y |- {x} === {y}
    have(singleton(x) === singleton(x)) by RightRefl
    thenHave((x === y) |- singleton(x) === singleton(y)) by RightSubstEq(List((x, y)), lambda(a, singleton(x) === singleton(a)))
    val bwd = thenHave((x === y) ==> (singleton(x) === singleton(y))) by Restate

    have((singleton(x) === singleton(y)) <=> (x === y)) by RightIff(fwd, bwd)
  }

  /**
   * Theorem --- Unordered pairs of elements of a set `x` are in its power set `P(x)`.
   *
   *    `a ∈ x ∧ b ∈ x <=> {a, b} ∈ P(x)`
   */
  val unorderedPairInPowerSet = Theorem(
    (in(a, x) /\ in(b, x)) <=> in(unorderedPair(a, b), powerSet(x))
  ) {

    // forward
    val fwd = have((in(a, x) /\ in(b, x)) ==> in(unorderedPair(a, b), powerSet(x))) subproof {
      val axExpansion = have(in(unorderedPair(a, b), powerSet(x)) <=> ∀(z, in(z, unorderedPair(a, b)) ==> in(z, x))) by Tautology.from(
        powerAxiom of (x -> unorderedPair(a, b), y -> x),
        subsetAxiom of (x -> unorderedPair(a, b), y -> x)
      )

      val abToz = have(in(a, x) /\ in(b, x) |- ∀(z, in(z, unorderedPair(a, b)) ==> in(z, x))) subproof {
        val pairAxab = have(in(z, unorderedPair(a, b)) |- (z === a) \/ (z === b)) by Tautology.from(pairAxiom of (x -> a, y -> b))

        have(in(a, x) /\ in(b, x) |- in(a, x)) by Restate
        val za = thenHave((in(a, x) /\ in(b, x), (z === a)) |- in(z, x)) by RightSubstEq(List((z, a)), lambda(a, in(a, x)))
        have(in(a, x) /\ in(b, x) |- in(b, x)) by Restate
        val zb = thenHave((in(a, x) /\ in(b, x), (z === b)) |- in(z, x)) by RightSubstEq(List((z, b)), lambda(a, in(a, x)))

        val zab = have((in(a, x) /\ in(b, x), (z === a) \/ (z === b)) |- in(z, x)) by LeftOr(za, zb)

        have((in(z, unorderedPair(a, b)), in(a, x) /\ in(b, x)) |- in(z, x)) by Cut(pairAxab, zab)
        thenHave(in(a, x) /\ in(b, x) |- in(z, unorderedPair(a, b)) ==> in(z, x)) by Restate
        thenHave(thesis) by RightForall
      }

      have(thesis) by Tautology.from(abToz, axExpansion)
    }

    val bwd = have(in(unorderedPair(a, b), powerSet(x)) ==> (in(a, x) /\ in(b, x))) subproof {
      have(in(unorderedPair(a, b), powerSet(x)) |- ∀(z, in(z, unorderedPair(a, b)) ==> in(z, x))) by Tautology.from(
        powerAxiom of (x -> unorderedPair(a, b), y -> x),
        subsetAxiom of (x -> unorderedPair(a, b), y -> x)
      )
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
   *  `pair(a, b) = {{a}, {a, b}}`
   *
   *  `pair(a, b) = pair(c, d) <=> a = c ∧ b = d`
   */
  val pairExtensionality = Theorem(
    (pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))
  ) {
    // forward direction
    //  (a === c) /\ (b === d) ==> pair a b === pair c d
    val fwd = have(((a === c) /\ (b === d)) ==> (pair(a, b) === pair(c, d))) subproof {
      have((pair(a, b) === pair(a, b))) by RightRefl
      thenHave(Set((a === c), (b === d)) |- (pair(a, b) === pair(c, d))) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(x, y), pair(a, b) === pair(x, y)))
      thenHave(thesis) by Restate
    }

    // backward direction
    //  pair a b === pair c d ==> (a === c) /\ (b === d)
    val bwd = have((pair(a, b) === pair(c, d)) ==> ((a === c) /\ (b === d))) subproof {
      have(((pair(a, b) === pair(c, d))) |- (pair(a, b) === pair(c, d))) by Hypothesis
      val lhs1 = thenHave(
        (
          (pair(a, b) === pair(c, d)),
          (unorderedPair(unorderedPair(a, b), singleton(a)) === unorderedPair(unorderedPair(c, d), singleton(c))) <=> (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(
            c
          ))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(a) === unorderedPair(c, d))))
        ) |- (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(c))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(a) === unorderedPair(c, d))))
      ) by RightSubstIff(
        List(
          (
            (unorderedPair(unorderedPair(a, b), singleton(a)) === unorderedPair(unorderedPair(c, d), singleton(c))),
            (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(c))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(a) === unorderedPair(c, d))))
          )
        ),
        lambda(h, h)
      )
      have(
        Set((pair(a, b) === pair(c, d))) |- (((unorderedPair(a, b) === unorderedPair(c, d)) /\ (singleton(a) === singleton(c))) \/ ((unorderedPair(a, b) === singleton(c)) /\ (singleton(
          a
        ) === unorderedPair(c, d))))
      ) by Cut(unorderedPairExtensionality of (a -> unorderedPair(a, b), b -> singleton(a), c -> unorderedPair(c, d), d -> singleton(c)), lhs1)
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> b, c -> c, d -> d))) // {a, b} = {c, d}
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> a, c -> c, d -> d))) //    {a} = {c, d}
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> b, c -> c, d -> c))) // {a, b} = {c}
      andThen(applySubst(unorderedPairExtensionality of (a -> a, b -> a, c -> c, d -> c))) //    {a} = {c}
      val expandedProp = thenHave(
        (
          (pair(a, b) === pair(c, d))
        ) |- ((((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))) /\ (((a === c) /\ (a === c)) \/ ((a === c) /\ (a === c)))) \/ ((((a === c) /\ (b === c)) \/ ((a === c) /\ (b === c))) /\ (((a === c) /\ (a === d)) \/ ((a === d) /\ (a === c))))
      ) by Restate
      val ac = thenHave(Set((pair(a, b) === pair(c, d))) |- (a === c)) by Tautology

      // required subproof, transitivity of equality
      // b = c, a = d, a = c |- b = d
      val transEqdb = have((d === a, a === c, c === b) |- d === b) subproof {
        val dac = have((d === a) /\ (a === c) |- (d === c)) by Restate.from(equalityTransitivity of (x -> d, y -> a, z -> c))
        have((d === c) /\ (c === b) |- (d === b)) by Restate.from(equalityTransitivity of (x -> d, y -> c, z -> b))
        val dcb = thenHave(Set((d === c), (c === b)) |- (d === b)) by Restate
        val db = have(((d === a) /\ (a === c), (c === b)) |- (d === b)) by Cut(dac, dcb)

        thenHave(thesis) by Restate
      }

      val db = have(((pair(a, b) === pair(c, d))) |- (a === c) /\ (b === d)) by Tautology.from(expandedProp, ac, transEqdb)
      thenHave(thesis) by Restate
    }

    have(thesis) by RightIff(fwd, bwd)
  }

  /**
   * Theorem --- No set is an element of itself.
   *
   *    `! x ∈ x`
   *
   * This is imposed by the Foundation Axiom ([[foundationAxiom]]).
   */
  val selfNonInclusion = Theorem(
    !in(x, x)
  ) {
    val X = singleton(x)

    have(!(X === ∅) ==> ∃(y, in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)))) by InstFunSchema(Map(x -> X))(foundationAxiom)
    val lhs = thenHave(!(X === ∅) |- ∃(y, in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)))) by Restate

    have(in(y, X) |- in(y, X) <=> (x === y)) by Weakening(singletonHasNoExtraElements)
    val innerRhs = thenHave(in(y, X) |- (x === y)) by Tautology

    have((in(x, X), (in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by Hypothesis
    thenHave((in(x, X), ∀(z, in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by LeftForall
    thenHave((in(x, X), ∀(z, in(z, X) ==> !in(z, x)), in(x, X)) |- in(x, X) ==> !in(x, x)) by InstFunSchema(Map(z -> x, y -> x))
    val coreRhs = thenHave(in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x)) |- !in(x, x)) by Restate

    // now we need to show that the assumption is indeed true
    // this requires destruction of the existential quantifier in lhs
    have(in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x)) |- in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x))) by Hypothesis
    val innerRhs2 = thenHave((in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)), x === y) |- in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x))) by LeftSubstEq(
      List((x, y)),
      lambda(Seq(y), in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)))
    )

    have((in(y, X), in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x))) by Cut(innerRhs, innerRhs2)
    thenHave(in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)) |- in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x))) by Restate
    val coreLhs = thenHave(∃(y, in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x))) by LeftExists

    val rhs = have(∃(y, in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y))) |- !in(x, x)) by Cut(coreLhs, coreRhs)

    val finRhs = have(!(X === ∅) |- !in(x, x)) by Cut(lhs, rhs)
    val finLhs = have(!(X === ∅)) by Restate.from(singletonNonEmpty)

    have(!in(x, x)) by Cut(finLhs, finRhs)
  }

  /**
   * Theorem --- No Universal Set
   *
   *    `∀ z. z ∈ x ⊢ ⊥`
   *
   * There does not exist a set of all sets. Alternatively, its existence, with
   * the [[comprehensionSchema]] and Russel's paradox ([[russelsParadox]]), produces
   * a contradiction.
   */
  val noUniversalSet = Theorem(
    ∀(z, in(z, x)) |- ()
  ) {
    have(in(x, x) |- ()) by Restate.from(selfNonInclusion)
    thenHave(∀(z, in(z, x)) |- ()) by LeftForall
  }

  /**
   * Theorem --- The power set of any set is not a proper subset of it.
   *
   *    `∃ x. P(x) ⊂ x ⊢ ⊥`
   */
  val powerSetNonInclusion = Theorem(
    exists(x, properSubset(powerSet(x), x)) |- ()
  ) {
    val lhs = have(subset(powerSet(x), x) |- subset(powerSet(x), x)) by Hypothesis

    val rhs = have(in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x)) by InstFunSchema(Map(x -> powerSet(x), y -> x))(powerAxiom)

    have(subset(powerSet(x), x) |- subset(powerSet(x), x) /\ (in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x))) by RightAnd(lhs, rhs)
    val contraLhs = thenHave(subset(powerSet(x), x) |- in(powerSet(x), powerSet(x))) by Tautology

    val contraRhs = have(!in(powerSet(x), powerSet(x))) by InstFunSchema(Map(x -> powerSet(x)))(selfNonInclusion)

    have(subset(powerSet(x), x) |- !in(powerSet(x), powerSet(x)) /\ in(powerSet(x), powerSet(x))) by RightAnd(contraLhs, contraRhs)
    thenHave(subset(powerSet(x), x) |- ()) by Restate
    thenHave(subset(powerSet(x), x) |- (x === powerSet(x))) by Weakening
    thenHave(properSubset(powerSet(x), x) |- ()) by Restate
    thenHave(∃(x, properSubset(powerSet(x), x)) |- ()) by LeftExists
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Operations on Sets
   */

  val setIntersectionUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))) by UniqueComprehension(x, lambda(Seq(t, z), in(t, y)))
  }

  /**
   * Binary Set Intersection --- Intersection of two sets.
   *
   *     `x ∩ y = {z ∈ x | z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val setIntersection = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))(setIntersectionUniqueness)

  val unaryIntersectionUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))))
  ) {
    val uniq = have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by UniqueComprehension(union(x), lambda(Seq(t, z), ∀(b, in(b, x) ==> in(t, b))))

    val lhs = have((in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))) |- ∀(b, in(b, x) ==> in(t, b)) /\ exists(b, in(b, x))) subproof {
      val unionAx = have(in(t, union(x)) |- exists(b, in(b, x) /\ in(t, b))) by Weakening(unionAxiom of (z -> t))

      have(in(b, x) /\ in(t, b) |- in(b, x)) by Restate
      thenHave(in(b, x) /\ in(t, b) |- exists(b, in(b, x))) by RightExists
      val exRed = thenHave(exists(b, in(b, x) /\ in(t, b)) |- exists(b, in(b, x))) by LeftExists

      have(in(t, union(x)) |- exists(b, in(b, x))) by Cut(unionAx, exRed)
      thenHave(thesis) by Weakening
    }

    val rhs = have(∀(b, in(b, x) ==> in(t, b)) /\ exists(b, in(b, x)) |- (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))) subproof {
      val unionAx = have(in(t, union(x)) <=> exists(z, in(z, x) /\ in(t, z))) by Restate.from(unionAxiom of (z -> t))

      have((in(b, x), in(b, x) ==> in(t, b)) |- in(b, x) /\ (in(t, b))) by Tautology
      thenHave((in(b, x), forall(b, in(b, x) ==> in(t, b))) |- in(b, x) /\ in(t, b)) by LeftForall
      thenHave((in(b, x), forall(b, in(b, x) ==> in(t, b))) |- exists(b, in(b, x) /\ in(t, b))) by RightExists
      val exRed = thenHave((exists(b, (in(b, x))), forall(b, in(b, x) ==> in(t, b))) |- exists(b, in(b, x) /\ in(t, b))) by LeftExists

      have(thesis) by Tautology.from(unionAx, exRed)
    }

    have(() |- (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))) <=> (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))) by Tautology.from(lhs, rhs)
    thenHave(() |- forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))) <=> (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by RightForall

    have(() |- forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))) <=> forall(t, (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by Cut(
      lastStep,
      universalEquivalenceDistribution of (P -> lambda(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))), Q -> lambda(
        t,
        (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))
      ))
    )
    thenHave(
      () |- forall(z, forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))) <=> forall(t, (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))))
    ) by RightForall

    have(
      () |- existsOne(z, forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) <=> existsOne(z, forall(t, (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))))
    ) by Cut(
      lastStep,
      uniqueExistentialEquivalenceDistribution of (P -> lambda(z, forall(t, in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))), Q -> lambda(
        z,
        forall(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))
      ))
    )
    have(thesis) by Tautology.from(lastStep, uniq)
  }

  /**
   * Unary Set Intersection --- Intersection of all elements of a given set.
   *
   *     `∩ x = {z ∈ ∪ x | ∀ y ∈ x. z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   */
  val unaryIntersection = DEF(x) --> The(z, ∀(t, in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))))(unaryIntersectionUniqueness)

  val setDifferenceUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))) by UniqueComprehension(x, lambda(Seq(t, z), !in(t, y)))
  }

  /**
   * Binary Set Difference --- Given two sets, produces the set that contains
   * elements in the first but not in the second.
   *
   *    `x - y = {z ∈ x | ! z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val setDifference = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))(setDifferenceUniqueness)

  /**
   * Theorem --- Intersection of a non-empty Class is a Set
   *
   * There exists a set that is the intersection of all sets satisfying a given
   * formula. With classes, this means that the unary intersection of a class
   * defined by a predicate is a set.
   *
   *    `∃ x. P(x) ⊢ ∃ z. t ∈ z ⇔ ∀ x. P(x) ⇒ t ∈ x`
   */
  val intersectionOfPredicateClassExists = Theorem(
    ∃(x, P(x)) |- ∃(z, ∀(t, in(t, z) <=> ∀(y, P(y) ==> in(t, y))))
  ) {
    have(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ sPhi(t, x))))) by InstFunSchema(Map(z -> x))(comprehensionSchema)

    val conjunction = thenHave(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, x), ∀(y, P(y) ==> in(t, y)))))

    have(∀(y, P(y) ==> in(t, y)) |- ∀(y, P(y) ==> in(t, y))) by Hypothesis
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- ∀(y, P(y) ==> in(t, y))) by Weakening
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- P(x) ==> in(t, x)) by InstantiateForall(x)
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- in(t, x) /\ ∀(y, P(y) ==> in(t, y))) by Tautology
    val fwd = thenHave(P(x) |- ∀(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Restate

    have((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) |- (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Hypothesis
    val bwd = thenHave((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) ==> (∀(y, P(y) ==> in(t, y)))) by Restate

    val lhs = have(P(x) |- ∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by RightIff(fwd, bwd)

    val form = formulaVariable
    have((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) |- in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Hypothesis
    val rhs = thenHave(
      Set((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))), (∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- (in(t, z) <=> (∀(y, P(y) ==> in(t, y))))
    ) by RightSubstIff(List((∀(y, P(y) ==> in(t, y)), (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))

    have((P(x), (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by Cut(lhs, rhs)
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by LeftForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y))))) by RightForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by RightExists
    val cutRhs = thenHave((P(x), ∃(z, ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists

    have(P(x) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by Cut(conjunction, cutRhs)
    thenHave(∃(x, P(x)) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists

  }

  /**
   * The first element of an ordered [[pair]] --- `first p = ∪ ∩ p`
   *
   * If `p = (a, b) = {{a}, {a, b}}`, `∩ p = {a}`, and `∪ ∩ p = a`.
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be used via
   * [[firstInPairReduction]].
   */
  val firstInPair = DEF(p) --> union(unaryIntersection(p))

  val secondInPairSingletonUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))
  ) {
    have(thesis) by UniqueComprehension(union(p), lambda(Seq(t, x), ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p))))))
  }

  /**
   * See [[secondInPair]].
   */
  val secondInPairSingleton =
    DEF(p) --> The(z, ∀(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))(secondInPairSingletonUniqueness)

  /**
   * The second element of an ordered [[pair]] ---
   *
   *    `second p = ∪ {x ∈ ∪ p | ∪ p != ∩ p ⟹ !x ∈ ∩ p} = ∪ (secondSingleton p)`
   *
   * There is a more naive definition: `second p = ∪ (∪ p - (first p))`.
   * If `p = (a, b) = {{a}, {a, b}}`, `∪ p = {a, b}`, and `∪ p - (first p)
   * = {a, b} - {a} = {b}`, the `∪` at the top level reduces this to `b`.
   * However, this fails when `a = b`, and returns the [[emptySet]].
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be used via
   * [[secondInPairReduction]].
   *
   * @see https://en.wikipedia.org/wiki/Ordered_pair#Kuratowski's_definition
   */
  val secondInPair = DEF(p) --> union(secondInPairSingleton(p))

  /**
   * Theorem --- The union of an ordered pair is the corresponding unordered pair.
   *
   *    `∪ (x, y) = ∪ {{x}, {x, y}} = {x, y}`
   */
  val unionOfOrderedPair = Lemma(
    () |- (union(pair(x, y)) === unorderedPair(x, y))
  ) {
    val upElem = have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by Restate.from(pairAxiom)

    val unionElem = have(in(z, union(pair(x, y))) <=> ((z === x) \/ (z === y))) subproof {
      // expand being in \cup (x, y)
      val unionax = have(in(z, union(pair(x, y))) <=> exists(b, in(b, pair(x, y)) /\ in(z, b))) by Restate.from(unionAxiom of x -> pair(x, y))

      // what does it mean for b to be in (x, y)?
      // b \in (x, y) /\ z \in b <=> z = x \/ z = y
      val fwd = have(exists(b, in(b, pair(x, y)) /\ in(z, b)) |- ((z === x) \/ (z === y))) subproof {
        val bxy =
          have(in(b, pair(x, y)) /\ in(z, b) |- ((b === unorderedPair(x, y)) \/ (b === unorderedPair(x, x)))) by Weakening(pairAxiom of (x -> unorderedPair(x, y), y -> unorderedPair(x, x), z -> b))
        val zxy = have((b === unorderedPair(x, y)) |- in(z, b) <=> ((z === x) \/ (z === y))) by Substitution.apply2(true, b === unorderedPair(x, y))(pairAxiom)
        val zxx = have((b === unorderedPair(x, x)) |- in(z, b) <=> ((z === x) \/ (z === x))) by Substitution.apply2(true, b === unorderedPair(x, x))(pairAxiom of y -> x)

        have(in(b, pair(x, y)) /\ in(z, b) |- ((z === x) \/ (z === y))) by Tautology.from(bxy, zxy, zxx)
        thenHave(thesis) by LeftExists
      }

      val bwd = have(((z === x) \/ (z === y)) |- exists(b, in(b, pair(x, y)) /\ in(z, b))) subproof {
        val xyp = have(in(unorderedPair(x, y), pair(x, y))) by Restate.from(firstElemInPair of (x -> unorderedPair(x, y), y -> unorderedPair(x, x)))
        val zx = have((z === x) |- in(z, unorderedPair(x, y))) by Substitution.apply2(true, z === x)(firstElemInPair)
        val zy = have((z === y) |- in(z, unorderedPair(x, y))) by Substitution.apply2(true, z === y)(secondElemInPair)

        have(((z === x) \/ (z === y)) |- in(unorderedPair(x, y), pair(x, y)) /\ in(z, unorderedPair(x, y))) by Tautology.from(xyp, zx, zy)
        thenHave(thesis) by RightExists
      }

      have(thesis) by Tautology.from(fwd, bwd, unionax)
    }

    have(in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y))) by Tautology.from(upElem, unionElem)
    thenHave(forall(z, in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y)))) by RightForall
    have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> union(pair(x, y)), y -> unorderedPair(x, y)))
  }

  /**
   * Theorem --- The unary intersection of an ordered pair is the singleton
   * containing the first element.
   *
   *    `∩ (x, y) = ∩ {{x}, {x, y}} = {x}`
   */
  val pairUnaryIntersection = Lemma(
    () |- in(z, unaryIntersection(pair(x, y))) <=> (z === x)
  ) {
    have(forall(t, in(t, unaryIntersection(pair(x, y))) <=> (exists(b, in(b, pair(x, y))) /\ ∀(b, in(b, pair(x, y)) ==> in(t, b))))) by InstantiateForall(unaryIntersection(pair(x, y)))(
      unaryIntersection.definition of (x -> pair(x, y))
    )
    val defexp = thenHave(in(z, unaryIntersection(pair(x, y))) <=> (exists(b, in(b, pair(x, y))) /\ ∀(b, in(b, pair(x, y)) ==> in(z, b)))) by InstantiateForall(z)

    val lhs = have(in(z, unaryIntersection(pair(x, y))) |- (z === x)) subproof {
      have(in(z, unaryIntersection(pair(x, y))) |- forall(b, in(b, pair(x, y)) ==> in(z, b))) by Weakening(defexp)
      thenHave(in(z, unaryIntersection(pair(x, y))) |- in(unorderedPair(x, x), pair(x, y)) ==> in(z, unorderedPair(x, x))) by InstantiateForall(unorderedPair(x, x))
      have(thesis) by Tautology.from(lastStep, secondElemInPair of (x -> unorderedPair(x, y), y -> unorderedPair(x, x)), singletonHasNoExtraElements of (y -> z))
    }

    val rhs = have((z === x) |- in(z, unaryIntersection(pair(x, y)))) subproof {
      val xinxy = have(in(x, unaryIntersection(pair(x, y)))) subproof {
        have(in(unorderedPair(x, x), pair(x, y))) by Restate.from(secondElemInPair of (x -> unorderedPair(x, y), y -> unorderedPair(x, x)))
        val exClause = thenHave(exists(b, in(b, pair(x, y)))) by RightExists

        have(in(b, pair(x, y)) |- in(b, pair(x, y))) by Hypothesis
        val bp = thenHave(in(b, pair(x, y)) |- (b === singleton(x)) \/ (b === unorderedPair(x, y))) by Substitution.apply2(false, pairAxiom of (z -> b, y -> singleton(x), x -> unorderedPair(x, y)))

        have(in(x, singleton(x))) by Restate.from(singletonHasNoExtraElements of (y -> x))
        val bxx = thenHave((b === singleton(x)) |- in(x, b)) by Substitution.apply2(true, (b === singleton(x)))

        have(in(x, unorderedPair(x, y))) by Restate.from(firstElemInPair)
        val bxy = thenHave((b === unorderedPair(x, y)) |- in(x, b)) by Substitution.apply2(true, (b === unorderedPair(x, y)))

        have(in(b, pair(x, y)) ==> in(x, b)) by Tautology.from(bp, bxx, bxy)
        val frClause = thenHave(forall(b, in(b, pair(x, y)) ==> in(x, b))) by RightForall

        have(thesis) by Tautology.from(defexp of (z -> x), exClause, frClause)
      }
      thenHave(thesis) by Substitution.apply2(true, (z === x))
    }

    have(thesis) by Tautology.from(lhs, rhs)
  }

  /**
   * Theorem --- The unary intersection and union of an ordered pair are equal
   * iff the two elements are equal.
   *
   *    `∪ (x, y) = {x} = {x, y} = ∩ (x, y) <=> x = y`
   *
   * See [[pairUnaryIntersection]] and [[unionOfOrderedPair]].
   */
  val pairUnionIntersectionEqual = Lemma(
    () |- (union(pair(x, y)) === unaryIntersection(pair(x, y))) <=> (x === y)
  ) {
    have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by Restate.from(pairAxiom)
    val unionPair = thenHave(in(z, union(pair(x, y))) <=> ((z === x) \/ (z === y))) by Substitution.apply2(true, unionOfOrderedPair)

    val fwd = have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (x === y)) subproof {
      have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- forall(z, in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y))))) by Weakening(
        extensionalityAxiom of (x -> union(pair(x, y)), y -> unaryIntersection(pair(x, y)))
      )
      thenHave((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y)))) by InstantiateForall(z)

      have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (((z === x) \/ (z === y)) <=> (z === x))) by Tautology.from(lastStep, unionPair, pairUnaryIntersection)
      thenHave((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (((y === x) \/ (y === y)) <=> (y === x))) by InstFunSchema(Map(z -> y))
      thenHave(thesis) by Restate
    }

    val bwd = have((x === y) |- (union(pair(x, y)) === unaryIntersection(pair(x, y)))) subproof {
      have((x === y) |- in(z, union(pair(x, y))) <=> ((z === x) \/ (z === x))) by Substitution.apply2(true, x === y)(unionPair)
      have((x === y) |- in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y)))) by Tautology.from(lastStep, pairUnaryIntersection)
      thenHave((x === y) |- forall(z, in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y))))) by RightForall

      have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> union(pair(x, y)), y -> unaryIntersection(pair(x, y))))
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

  /**
   * Theorem --- The [[firstInPair]] operation when applied to an ordered pair
   * produces the first element of the pair.
   *
   *    `first((x, y)) = x`
   */
  val firstInPairReduction = Lemma(
    () |- (firstInPair(pair(x, y)) === x)
  ) {
    // z \in \cap (x, y) <=> z = x
    val elemInter = have(in(z, unaryIntersection(pair(x, y))) <=> (z === x)) by Restate.from(pairUnaryIntersection)

    // z in \cup \cap p <=> z \in x
    val elemUnion = have(in(z, union(unaryIntersection(pair(x, y)))) <=> in(z, x)) subproof {
      val unionax =
        have(in(z, union(unaryIntersection(pair(x, y)))) <=> exists(t, in(t, unaryIntersection(pair(x, y))) /\ in(z, t))) by Restate.from(unionAxiom of (x -> unaryIntersection(pair(x, y))))

      val lhs = have(exists(t, in(t, unaryIntersection(pair(x, y))) /\ in(z, t)) |- in(z, x)) subproof {
        have(in(z, t) |- in(z, t)) by Hypothesis
        thenHave((in(z, t), (t === x)) |- in(z, x)) by Substitution.apply2(false, t === x)
        have(in(t, unaryIntersection(pair(x, y))) /\ in(z, t) |- in(z, x)) by Tautology.from(lastStep, elemInter of (z -> t))
        thenHave(thesis) by LeftExists
      }

      val rhs = have(in(z, x) |- exists(t, in(t, unaryIntersection(pair(x, y))) /\ in(z, t))) subproof {
        have(in(x, unaryIntersection(pair(x, y)))) by Restate.from(elemInter of (z -> x))
        thenHave(in(z, x) |- in(x, unaryIntersection(pair(x, y))) /\ in(z, x)) by Tautology
        thenHave(thesis) by RightExists
      }

      have(thesis) by Tautology.from(lhs, rhs, unionax)
    }

    thenHave(forall(z, in(z, union(unaryIntersection(pair(x, y)))) <=> in(z, x))) by RightForall

    // \cup \cap (x, y) = x
    val unioneq = have(union(unaryIntersection(pair(x, y))) === x) by Tautology.from(lastStep, extensionalityAxiom of (x -> union(unaryIntersection(pair(x, y))), y -> x))
    have((firstInPair(pair(x, y)) === union(unaryIntersection(pair(x, y))))) by InstantiateForall(firstInPair(pair(x, y)))(firstInPair.definition of (p -> pair(x, y)))
    have(thesis) by Substitution.apply2(true, lastStep)(unioneq)
  }

  /**
   * Theorem --- The [[secondInPairSingletone]] operation when applied to an
   * ordered pair produces the singleton containing the second element of the pair.
   *
   *    `secondSingleton((x, y)) = {y}`
   *
   * Used for [[secondInPair]] reduction.
   */
  val secondInPairSingletonReduction = Lemma(
    () |- in(z, secondInPairSingleton(pair(x, y))) <=> (z === y)
  ) {
    have(
      forall(
        t,
        in(t, secondInPairSingleton(pair(x, y))) <=> (in(t, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(t, unaryIntersection(pair(x, y))))))
      )
    ) by InstantiateForall(secondInPairSingleton(pair(x, y)))(secondInPairSingleton.definition of p -> pair(x, y))
    val sipsDef = thenHave(
      in(z, secondInPairSingleton(pair(x, y))) <=> (in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y))))))
    ) by InstantiateForall(z)

    val predElem = have((in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y)))))) <=> (z === y)) subproof {

      // breakdown for each of the clauses in the statement
      have(forall(z, in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y)))) by Tautology.from(unionOfOrderedPair, extensionalityAxiom of (x -> union(pair(x, y)), y -> unorderedPair(x, y)))
      thenHave(in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y))) by InstantiateForall(z)
      val zUnion = have(in(z, union(pair(x, y))) <=> ((z === x) \/ (z === y))) by Tautology.from(lastStep, pairAxiom)
      val unEqInt = have((union(pair(x, y)) === unaryIntersection(pair(x, y))) <=> (x === y)) by Restate.from(pairUnionIntersectionEqual)
      val zInter = have(in(z, unaryIntersection(pair(x, y))) <=> (z === x)) by Restate.from(pairUnaryIntersection)

      have(
        (in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y)))))) <=> (in(z, union(pair(x, y))) /\ ((!(union(
          pair(x, y)
        ) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y))))))
      ) by Restate
      val propDest = thenHave(
        (in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(
          z,
          unaryIntersection(pair(x, y))
        )))) <=> (((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))))
      ) by Substitution.apply2(false, zUnion, zInter, unEqInt)

      have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x)))) <=> (z === y)) subproof {
        val hypo = have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x)))) |- (((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))))) by Hypothesis
        thenHave((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), (x === y)) |- (((z === y) \/ (z === y)) /\ ((!(y === y)) ==> (!(z === x))))) by Substitution.apply2(false, x === y)
        val xeqy = thenHave((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), (x === y)) |- (z === y)) by Tautology

        have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), !(x === y)) |- (((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))))) by Weakening(hypo)
        val xneqy = thenHave((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), !(x === y)) |- (z === y)) by Tautology

        have(thesis) by Tautology.from(xeqy, xneqy, equalityTransitivity of (z -> y, y -> z))
      }

      have(thesis) by Tautology.from(lastStep, propDest)
    }

    have(thesis) by Tautology.from(sipsDef, predElem)
  }

  /**
   * Theorem --- The [[secondInPair]] operation when applied to an ordered pair
   * produces the second element of the pair.
   *
   *    `second((x, y)) = y`
   */
  val secondInPairReduction = Lemma(
    () |- secondInPair(pair(x, y)) === y
  ) {
    have(secondInPair(pair(x, y)) === union(secondInPairSingleton(pair(x, y)))) by InstantiateForall(secondInPair(pair(x, y)))(secondInPair.definition of p -> pair(x, y))
    have(forall(z, in(z, secondInPair(pair(x, y))) <=> in(z, union(secondInPairSingleton(pair(x, y)))))) by Tautology.from(
      lastStep,
      extensionalityAxiom of (x -> secondInPair(pair(x, y)), y -> union(secondInPairSingleton(pair(x, y))))
    )
    thenHave(in(z, secondInPair(pair(x, y))) <=> in(z, union(secondInPairSingleton(pair(x, y))))) by InstantiateForall(z)
    val secondElem =
      have(in(z, secondInPair(pair(x, y))) <=> (exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b)))) by Tautology.from(lastStep, unionAxiom of (x -> secondInPairSingleton(pair(x, y))))

    val elemIsY = have((exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b))) <=> in(z, y)) subproof {
      val lhs = have((exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b))) |- in(z, y)) subproof {
        have(in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b) |- in(z, b)) by Restate
        thenHave((in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b), (b === y)) |- in(z, y)) by Substitution.apply2(false, b === y)
        have((in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b)) |- in(z, y)) by Tautology.from(lastStep, secondInPairSingletonReduction of z -> b)

        thenHave(thesis) by LeftExists
      }

      val rhs = have(in(z, y) |- exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b))) subproof {
        have(in(z, y) |- in(z, y)) by Hypothesis
        have(in(z, y) |- in(y, secondInPairSingleton(pair(x, y))) /\ in(z, y)) by Tautology.from(lastStep, secondInPairSingletonReduction of z -> y)
        thenHave(thesis) by RightExists
      }

      have(thesis) by Tautology.from(lhs, rhs)
    }

    have(in(z, secondInPair(pair(x, y))) <=> in(z, y)) by Tautology.from(secondElem, elemIsY)
    thenHave(forall(z, in(z, secondInPair(pair(x, y))) <=> in(z, y))) by RightForall
    have(thesis) by Tautology.from(lastStep, extensionalityAxiom of x -> secondInPair(pair(x, y)))
  }

  /**
   * Cartesian Products and Relations
   */

  val cartesianProductUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))) by UniqueComprehension(
      powerSet(powerSet(setUnion(x, y))),
      lambda(Seq(t, z), ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))
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
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val cartesianProduct =
    DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))(cartesianProductUniqueness)

  /**
   * Theorem --- cartesian Product ([[cartesianProd]]) of any set with the
   * [[emptySet]] is empty.
   */
  val productWithEmptySetEmpty = Theorem(
    () |- (cartesianProduct(x, emptySet()) === emptySet()) /\ (cartesianProduct(emptySet(), x) === emptySet())
  ) {
    val xFirst = have(() |- (cartesianProduct(x, emptySet()) === emptySet())) subproof {
      have(
        forall(t, in(t, cartesianProduct(x, emptySet())) <=> (in(t, powerSet(powerSet(setUnion(x, emptySet())))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet())))))
      ) by InstantiateForall(cartesianProduct(x, emptySet()))(cartesianProduct.definition of (y -> emptySet()))
      val impl = thenHave(
        in(t, cartesianProduct(x, emptySet())) <=> (in(t, powerSet(powerSet(setUnion(x, emptySet())))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet()))))
      ) by InstantiateForall(t)

      val elemEmpty = have(in(t, emptySet()) <=> (in(t, powerSet(powerSet(setUnion(x, emptySet())))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet()))))) subproof {
        val lhs = have(in(t, emptySet()) |- (in(t, powerSet(powerSet(setUnion(x, emptySet())))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet()))))) by Weakening(
          emptySet.definition of (x -> t)
        )

        have((t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet()) |- in(t, emptySet())) by Weakening(emptySet.definition of (x -> b))
        thenHave(exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet())) |- in(t, emptySet())) by LeftExists
        thenHave(exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet()))) |- in(t, emptySet())) by LeftExists
        val rhs = thenHave(in(t, powerSet(powerSet(setUnion(x, emptySet())))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet()))) |- in(t, emptySet())) by Weakening

        have(thesis) by Tautology.from(lhs, rhs)
      }

      have(in(t, cartesianProduct(x, emptySet())) <=> in(t, emptySet())) by Tautology.from(impl, elemEmpty)
      val ext = thenHave(forall(t, in(t, cartesianProduct(x, emptySet())) <=> in(t, emptySet()))) by RightForall

      have(thesis) by Tautology.from(ext, extensionalityAxiom of (x -> cartesianProduct(x, emptySet()), y -> emptySet()))
    }

    val xSecond = have(() |- (cartesianProduct(emptySet(), x) === emptySet())) subproof {
      have(
        forall(t, in(t, cartesianProduct(emptySet(), y)) <=> (in(t, powerSet(powerSet(setUnion(emptySet(), y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y)))))
      ) by InstantiateForall(cartesianProduct(emptySet(), y))(cartesianProduct.definition of (x -> emptySet()))
      val impl = thenHave(
        in(t, cartesianProduct(emptySet(), y)) <=> (in(t, powerSet(powerSet(setUnion(emptySet(), y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y))))
      ) by InstantiateForall(t)

      val elemEmpty = have(in(t, emptySet()) <=> (in(t, powerSet(powerSet(setUnion(emptySet(), y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y))))) subproof {
        val lhs = have(in(t, emptySet()) |- (in(t, powerSet(powerSet(setUnion(emptySet(), y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y))))) by Weakening(
          emptySet.definition of (x -> t)
        )

        have((t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y) |- in(t, emptySet())) by Weakening(emptySet.definition of (x -> a))
        thenHave(exists(b, (t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y)) |- in(t, emptySet())) by LeftExists
        thenHave(exists(a, exists(b, (t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y))) |- in(t, emptySet())) by LeftExists
        val rhs = thenHave(in(t, powerSet(powerSet(setUnion(emptySet(), y)))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, emptySet()) /\ in(b, y))) |- in(t, emptySet())) by Weakening

        have(thesis) by Tautology.from(lhs, rhs)
      }

      have(in(t, cartesianProduct(emptySet(), y)) <=> in(t, emptySet())) by Tautology.from(impl, elemEmpty)
      val ext = thenHave(forall(t, in(t, cartesianProduct(emptySet(), y)) <=> in(t, emptySet()))) by RightForall

      have(thesis) by Tautology.from(ext of (y -> x), extensionalityAxiom of (x -> cartesianProduct(emptySet(), x), y -> emptySet()))
    }

    have(thesis) by RightAnd(xFirst, xSecond)
  }

  /**
   * Theorem --- a pair is in the product `x * y` iff its elements are in `x` and
   * `y` respectively.
   *
   *    `(a, b) ∈ x * y <=> a ∈ x ∧ b ∈ y`
   */
  val pairInCartesianProduct = Theorem(
    in(pair(a, b), cartesianProduct(x, y)) <=> (in(a, x) /\ in(b, y))
  ) {
    have(
      (cartesianProduct(x, y) === cartesianProduct(x, y)) <=> ∀(
        t,
        in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))))
      )
    ) by InstantiateForall(cartesianProduct(x, y))(cartesianProduct.definition)
    thenHave(∀(t, in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y)))))) by Restate
    val cartProdDef = thenHave(
      in(pair(a, b), cartesianProduct(x, y)) <=> (in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) /\ ∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y))))
    ) by InstantiateForall(pair(a, b))

    // forward
    // (a, b) \in x * y ⟹ a ∈ x ∧ b ∈ y
    val fwd = have(in(pair(a, b), cartesianProduct(x, y)) ==> (in(a, x) /\ in(b, y))) subproof {
      have((a === c, b === d, in(c, x) /\ in(d, y)) |- in(c, x) /\ in(d, y)) by Hypothesis
      thenHave((a === c, b === d, in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(a, b), in(a, x) /\ in(b, y)))
      thenHave(Set((a === c) /\ (b === d), in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by Restate
      andThen(applySubst(pairExtensionality))
      thenHave((pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y) |- in(a, x) /\ in(b, y)) by Restate
      thenHave(∃(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by LeftExists
      thenHave(∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(a, x) /\ in(b, y)) by LeftExists
      val cdExists = thenHave((in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) /\ ∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(a, x) /\ in(b, y))) by Weakening
      have(thesis) by Tautology.from(cdExists, cartProdDef)
    }
    // backward
    // a \in x /\ b \in y ==> (a, b) \in x * y
    val bwd = have(in(a, x) /\ in(b, y) ==> in(pair(a, b), cartesianProduct(x, y))) subproof {
      val membership = have(in(a, x) /\ in(b, y) |- in(pair(a, b), powerSet(powerSet(setUnion(x, y))))) subproof {
        val powerSubsetDef = have(in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) <=> ∀(z, in(z, pair(a, b)) ==> in(z, powerSet(setUnion(x, y))))) by Tautology.from(
          powerAxiom of (x -> pair(a, b), y -> powerSet(setUnion(x, y))),
          subsetAxiom of (x -> pair(a, b), y -> powerSet(setUnion(x, y)))
        )

        val unionToPower = have((in(a, setUnion(x, y)) /\ in(b, setUnion(x, y)), in(z, pair(a, b))) |- in(z, powerSet(setUnion(x, y)))) subproof {
          val zabHypo = have(in(z, pair(a, b)) |- in(z, pair(a, b))) by Hypothesis
          val cutLhs = have(in(z, pair(a, b)) |- (z === unorderedPair(a, b)) \/ (z === singleton(a))) by Tautology.from(zabHypo, pairAxiom of (x -> unorderedPair(a, b), y -> singleton(a)))

          // need to show that {a, b} and {a} = {a, a} are in P(x \cup y)
          val prem = (in(a, setUnion(x, y)) /\ in(b, setUnion(x, y)))

          have(prem |- in(unorderedPair(a, b), powerSet(setUnion(x, y)))) by Weakening(unorderedPairInPowerSet of (x -> setUnion(x, y)))
          val zab = thenHave((prem, (z === unorderedPair(a, b))) |- in(z, powerSet(setUnion(x, y)))) by RightSubstEq(List((z, unorderedPair(a, b))), lambda(a, in(a, powerSet(setUnion(x, y)))))
          have(prem |- in(unorderedPair(a, a), powerSet(setUnion(x, y)))) by Weakening(unorderedPairInPowerSet of (x -> setUnion(x, y), b -> a))
          val zaa = thenHave((prem, (z === unorderedPair(a, a))) |- in(z, powerSet(setUnion(x, y)))) by RightSubstEq(List((z, unorderedPair(a, a))), lambda(a, in(a, powerSet(setUnion(x, y)))))

          val cutRhs = have((prem, (z === unorderedPair(a, b)) \/ (z === singleton(a))) |- in(z, powerSet(setUnion(x, y)))) by LeftOr(zab, zaa)

          have(thesis) by Cut(cutLhs, cutRhs)
        }

        val abToUnion = have(in(a, x) /\ in(b, y) |- in(a, setUnion(x, y)) /\ in(b, setUnion(x, y))) subproof {
          have(in(a, x) |- in(a, setUnion(x, y)) <=> (in(a, x) \/ in(a, y))) by Weakening(setUnionMembership of (z -> a))
          val aUn = thenHave(in(a, x) |- in(a, setUnion(x, y))) by Tautology
          have(in(b, y) |- in(b, setUnion(x, y)) <=> (in(b, x) \/ in(b, y))) by Weakening(setUnionMembership of (z -> b))
          val bUn = thenHave(in(b, y) |- in(b, setUnion(x, y))) by Tautology

          have((in(a, x), in(b, y)) |- in(a, setUnion(x, y)) /\ in(b, setUnion(x, y))) by RightAnd(aUn, bUn)
          thenHave(thesis) by Restate
        }

        have((in(a, x) /\ in(b, y), in(z, pair(a, b))) |- in(z, powerSet(setUnion(x, y)))) by Cut(abToUnion, unionToPower)
        thenHave((in(a, x) /\ in(b, y)) |- in(z, pair(a, b)) ==> in(z, powerSet(setUnion(x, y)))) by Restate
        val abToPower = thenHave((in(a, x) /\ in(b, y)) |- ∀(z, in(z, pair(a, b)) ==> in(z, powerSet(setUnion(x, y))))) by RightForall

        have(thesis) by Tautology.from(abToPower, powerSubsetDef)
      }

      val filtering = have(in(a, x) /\ in(b, y) |- ∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)))) subproof {
        have(in(a, x) /\ in(b, y) |- (pair(a, b) === pair(a, b)) /\ in(a, x) /\ in(b, y)) by Restate
        thenHave(in(a, x) /\ in(b, y) |- ∃(d, (pair(a, d) === pair(a, b)) /\ in(a, x) /\ in(d, y))) by RightExists
        thenHave(in(a, x) /\ in(b, y) |- ∃(c, ∃(d, (pair(c, d) === pair(a, b)) /\ in(c, x) /\ in(d, y)))) by RightExists
      }

      val compCriterion =
        have(in(a, x) /\ in(b, y) |- in(pair(a, b), powerSet(powerSet(setUnion(x, y)))) /\ ∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)))) by RightAnd(membership, filtering)

      have(thesis) by Tautology.from(compCriterion, cartProdDef)
    }

    have(thesis) by RightIff(fwd, bwd)
  }

  /**
   * Theorem --- If `t` is a pair containing elements from `x` and `y`, then
   * it is in `PP(x ∪ y)`.
   *
   *    `∃ c, d. t = (c, d) ∧ c ∈ x ∧ d ∈ y ⊢ t ∈ PP(x ∪ y)`
   *
   * Asserts that the first part of the [[cartesianProduct]] definition is redundant.
   */
  val elemOfPowerPowerUnion = Lemma(
    ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))
  ) {
    val upCD = have((in(c, x), in(d, y)) |- in(unorderedPair(c, d), powerSet(setUnion(x, y)))) subproof {

      have((in(c, x), in(d, y)) |- subset(unorderedPair(c, d), setUnion(x, y))) subproof {
        val zcd = have(in(z, unorderedPair(c, d)) <=> ((z === c) \/ (z === d))) by Restate.from(pairAxiom of (x -> c, y -> d))
        val zunion = have(in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))) by Restate.from(setUnionMembership)

        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.apply2(false, z === c)(zunion)
        val zd = have((z === d) |- in(z, setUnion(x, y)) <=> (in(d, x) \/ in(d, y))) by Substitution.apply2(false, z === d)(zunion)

        have((in(c, x), in(d, y)) |- in(z, unorderedPair(c, d)) ==> in(z, setUnion(x, y))) by Tautology.from(zcd, zc, zd)
        thenHave((in(c, x), in(d, y)) |- forall(z, in(z, unorderedPair(c, d)) ==> in(z, setUnion(x, y)))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> unorderedPair(c, d), y -> setUnion(x, y)))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y -> setUnion(x, y), x -> unorderedPair(c, d)))
    }

    val upCC = have((in(c, x)) |- in(unorderedPair(c, c), powerSet(setUnion(x, y)))) subproof {

      have((in(c, x)) |- subset(unorderedPair(c, c), setUnion(x, y))) subproof {
        val zcd = have(in(z, unorderedPair(c, c)) <=> (z === c)) by Restate.from(pairAxiom of (x -> c, y -> c))
        val zunion = have(in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))) by Restate.from(setUnionMembership)

        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.apply2(false, z === c)(zunion)

        have(in(c, x) |- in(z, unorderedPair(c, c)) ==> in(z, setUnion(x, y))) by Tautology.from(zcd, zc)
        thenHave(in(c, x) |- forall(z, in(z, unorderedPair(c, c)) ==> in(z, setUnion(x, y)))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> unorderedPair(c, c), y -> setUnion(x, y)))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y -> setUnion(x, y), x -> unorderedPair(c, c)))

    }

    have((in(c, x), in(d, y)) |- in(pair(c, d), powerSet(powerSet(setUnion(x, y))))) subproof {

      have((in(c, x), in(d, y)) |- subset(pair(c, d), powerSet(setUnion(x, y)))) subproof {
        val zp = have(in(z, pair(c, d)) <=> ((z === unorderedPair(c, d)) \/ (z === unorderedPair(c, c)))) by Restate.from(pairAxiom of (x -> unorderedPair(c, d), y -> unorderedPair(c, c)))

        val zcc = have((z === unorderedPair(c, c), in(c, x)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.apply2(true, z === unorderedPair(c, c))(upCC)
        val zcd = have((z === unorderedPair(c, d), in(c, x), in(d, y)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.apply2(true, z === unorderedPair(c, d))(upCD)

        have((in(c, x), in(d, y)) |- in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y)))) by Tautology.from(zp, zcc, zcd)
        thenHave((in(c, x), in(d, y)) |- forall(z, in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y))))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> pair(c, d), y -> powerSet(setUnion(x, y))))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y -> powerSet(setUnion(x, y)), x -> pair(c, d)))

    }

    thenHave((t === pair(c, d), in(c, x), in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Substitution.apply2(true, t === pair(c, d))
    thenHave(((t === pair(c, d)) /\ in(c, x) /\ in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Restate
    thenHave(exists(d, ((t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))) by LeftExists
    thenHave(thesis) by LeftExists
  }

  /**
   * Theorem --- the binary set union operation is commutative.
   *
   *    `a ∪ b = b ∪ a`
   */
  val unionCommutativity = Lemma(
    setUnion(a, b) === setUnion(b, a)
  ) {
    have(in(z, setUnion(a, b)) <=> in(z, setUnion(b, a))) by Tautology.from(setUnionMembership of (x -> a, y -> b), setUnionMembership of (x -> b, y -> a))
    thenHave(forall(z, in(z, setUnion(a, b)) <=> in(z, setUnion(b, a)))) by RightForall

    have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> setUnion(a, b), y -> setUnion(b, a)))
  }

  /**
   * Theorem --- the first element of a union is a subset of it.
   *
   *    `a ⊆ a ∪ b`
   */
  val unionSubsetFirst = Lemma(
    subset(a, setUnion(a, b))
  ) {
    have(in(z, a) ==> in(z, setUnion(a, b))) by Weakening(setUnionMembership of (x -> a, y -> b))
    thenHave(forall(z, in(z, a) ==> in(z, setUnion(a, b)))) by RightForall

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> a, y -> setUnion(a, b)))
  }

  /**
   * Theorem --- the second element of a union is a subset of it.
   *
   *    `a ⊆ a ∪ b`
   */
  val unionSubsetSecond = Lemma(
    subset(b, setUnion(a, b))
  ) {
    have(thesis) by Substitution.apply2(true, unionCommutativity)(unionSubsetFirst of (a -> b, b -> a))
  }

  /**
   * Theorem --- the union of two subsets of a set is still a subset of it.
   *
   *    `a ⊆ c ∧ b ⊆ c ⊢ a ∪ b ⊆ c`
   */
  val unionOfTwoSubsets = Lemma(
    subset(a, c) /\ subset(b, c) |- subset(setUnion(a, b), c)
  ) {
    val unionDef = have(in(z, setUnion(a, b)) <=> (in(z, a) \/ in(z, b))) by Restate.from(setUnionMembership of (x -> a, y -> b))

    have(subset(a, c) |- forall(z, in(z, a) ==> in(z, c))) by Weakening(subsetAxiom of (x -> a, y -> c))
    val ac = thenHave(subset(a, c) |- in(z, a) ==> in(z, c)) by InstantiateForall(z)
    val bc = ac of a -> b

    have(subset(a, c) /\ subset(b, c) |- in(z, setUnion(a, b)) ==> in(z, c)) by Tautology.from(unionDef, ac, bc)
    thenHave(subset(a, c) /\ subset(b, c) |- forall(z, in(z, setUnion(a, b)) ==> in(z, c))) by RightForall

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> setUnion(a, b), y -> c))
  }

  /**
   * Theorem --- the union of subsets of two sets is a subset of their union.
   *
   *    `a ⊆ c ∧ b ⊆ d ⊢ a ∪ b ⊆ c ∪ d`
   */
  val unionOfSubsetsOfDifferentSets = Lemma(
    subset(a, c) /\ subset(b, d) |- subset(setUnion(a, b), setUnion(c, d))
  ) {
    val unionDefab = have(in(z, setUnion(a, b)) <=> (in(z, a) \/ in(z, b))) by Restate.from(setUnionMembership of (x -> a, y -> b))
    val unionDefcd = unionDefab of (a -> c, b -> d)

    have(subset(a, c) |- forall(z, in(z, a) ==> in(z, c))) by Weakening(subsetAxiom of (x -> a, y -> c))
    val ac = thenHave(subset(a, c) |- in(z, a) ==> in(z, c)) by InstantiateForall(z)
    val bc = ac of (a -> b, c -> d)

    have(subset(a, c) /\ subset(b, d) |- in(z, setUnion(a, b)) ==> (in(z, c) \/ in(z, d))) by Tautology.from(unionDefab, ac, bc)
    thenHave(subset(a, c) /\ subset(b, d) |- in(z, setUnion(a, b)) ==> in(z, setUnion(c, d))) by Substitution.apply2(true, unionDefcd)
    thenHave(subset(a, c) /\ subset(b, d) |- forall(z, in(z, setUnion(a, b)) ==> in(z, setUnion(c, d)))) by RightForall

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> setUnion(a, b), y -> setUnion(c, d)))
  }

  /**
   * Theorem --- the subset predicate is transitive.
   *
   *    `a ⊆ b ∧ b ⊆ c ⊢ a ⊆ c`
   */
  val subsetTransitivity = Lemma(
    subset(a, b) /\ subset(b, c) |- subset(a, c)
  ) {
    have(subset(a, b) |- forall(z, in(z, a) ==> in(z, b))) by Weakening(subsetAxiom of (x -> a, y -> b))
    val sab = thenHave(subset(a, b) |- in(z, a) ==> in(z, b)) by InstantiateForall(z)
    val sbc = sab of (a -> b, b -> c)

    have(subset(a, b) /\ subset(b, c) |- in(z, a) ==> in(z, c)) by Tautology.from(sab, sbc)
    thenHave(subset(a, b) /\ subset(b, c) |- forall(z, in(z, a) ==> in(z, c))) by RightForall

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> a, y -> c))
  }

  /**
   * Theorem --- a set is an element of a Cartesian product iff it is a pair containing
   * elements from the constituents of the product.
   *
   *    `t ∈ x * y <=> ∃ a, b. t = (a, b) ∧ a ∈ x ∧ b ∈ y`
   *
   * Asserts a stronger definition of the [[cartesianProduct]]. See
   * [[elemOfPowerPowerUnion]] for the redundancy proof.
   */
  val elemOfCartesianProduct = Theorem(
    in(t, cartesianProduct(x, y)) <=> ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))
  ) {
    have(forall(t, in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))))) by InstantiateForall(
      cartesianProduct(x, y)
    )(cartesianProduct.definition)
    val defUnfold = thenHave(in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))) by InstantiateForall(t)

    have(∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))))) by Tautology.from(
      elemOfPowerPowerUnion
    )

    have(thesis) by Tautology.from(lastStep, defUnfold)
  }

  /**
   * Theorem --- the union of two Cartesian products is a subset of the product of unions.
   *
   *    `a * b ∪ c * d ⊆ (a ∪ c) * (b ∪ d)`
   */
  val unionOfCartesianProducts = Lemma(
    subset(setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), cartesianProduct(setUnion(a, c), setUnion(b, d)))
  ) {
    val axb = cartesianProduct(a, b)
    val cxd = cartesianProduct(c, d)

    val unionDef = have(in(z, setUnion(axb, cxd)) |- in(z, axb) \/ in(z, cxd)) by Weakening(setUnionMembership of (x -> axb, y -> cxd))

    /*
      z in a x b
      <=>
      exist x, y. z = (x, y); x in a; y in b
      ==> x in a U c, y in b U d
      ==> z in (a U c) x (b U d)
     */
    val zab = have(in(z, axb) |- in(z, cartesianProduct(setUnion(a, c), setUnion(b, d)))) subproof {
      have(forall(z, in(z, a) ==> in(z, setUnion(a, c)))) by Tautology.from(unionSubsetFirst of (b -> c), subsetAxiom of (x -> a, y -> setUnion(a, c)))
      val xa = thenHave((in(x, a) ==> in(x, setUnion(a, c)))) by InstantiateForall(x)

      have(forall(z, in(z, b) ==> in(z, setUnion(b, d)))) by Tautology.from(unionSubsetFirst of (a -> b, b -> d), subsetAxiom of (x -> b, y -> setUnion(b, d)))
      val yb = thenHave((in(y, b) ==> in(y, setUnion(b, d)))) by InstantiateForall(y)

      have(in(x, a) /\ in(y, b) |- in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))) by Tautology.from(xa, yb)
      thenHave((z === pair(x, y)) /\ in(x, a) /\ in(y, b) |- (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))) by Tautology
      thenHave((z === pair(x, y)) /\ in(x, a) /\ in(y, b) |- exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d)))) by RightExists
      thenHave((z === pair(x, y)) /\ in(x, a) /\ in(y, b) |- exists(x, exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))))) by RightExists
      thenHave(exists(y, (z === pair(x, y)) /\ in(x, a) /\ in(y, b)) |- exists(x, exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))))) by LeftExists
      thenHave(exists(x, exists(y, (z === pair(x, y)) /\ in(x, a) /\ in(y, b))) |- exists(x, exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))))) by LeftExists

      have(thesis) by Tautology.from(lastStep, elemOfCartesianProduct of (x -> a, y -> b, t -> z), elemOfCartesianProduct of (x -> setUnion(a, c), y -> setUnion(b, d), t -> z))
    }

    val zcd = have(in(z, cxd) |- in(z, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Substitution.apply2(false, unionCommutativity of (a -> c, b -> a), unionCommutativity of (a -> d, b -> b))(
      lastStep of (a -> c, b -> d, c -> a, d -> b)
    )

    have(in(z, setUnion(axb, cxd)) ==> in(z, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Tautology.from(unionDef, zab, zcd)
    thenHave(forall(z, in(z, setUnion(axb, cxd)) ==> in(z, cartesianProduct(setUnion(a, c), setUnion(b, d))))) by RightForall

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> setUnion(axb, cxd), y -> cartesianProduct(setUnion(a, c), setUnion(b, d))))
  }

  /**
   * Theorem --- if a pair is in a set `r`, then elements of the pair are in `∪ ∪ r`.
   *
   *    `(a, b) ∈ r ⊢ a, b ∈ ∪ ∪ r`
   *
   * Used to prove stronger definitions for [[relationDomain]] and [[relationRange]]
   */
  val pairInSetImpliesPairInUnion = Theorem(
    in(pair(a, b), r) |- in(a, union(union(r))) /\ in(b, union(union(r)))
  ) {
    // a, b in {a, b} and union union r
    // {a, b} in union r
    // pair a b in r
    val unionUP = have(in(pair(a, b), r) |- in(unorderedPair(a, b), union(r))) subproof {
      val hypo = have(in(pair(a, b), r) |- in(pair(a, b), r)) by Hypothesis
      have(in(pair(a, b), r) |- in(unorderedPair(a, b), pair(a, b)) /\ in(pair(a, b), r)) by RightAnd(hypo, firstElemInPair of (x -> unorderedPair(a, b), y -> singleton(a)))
      thenHave(in(pair(a, b), r) |- ∃(y, in(unorderedPair(a, b), y) /\ in(y, r))) by RightExists
      andThen(applySubst(unionAxiom of (z -> unorderedPair(a, b), x -> r)))
    }
    val unionA = have(in(unorderedPair(a, b), union(r)) |- in(a, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(a, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, firstElemInPair of (x -> a, y -> b))
      thenHave(in(unorderedPair(a, b), union(r)) |- ∃(y, in(a, y) /\ in(y, union(r)))) by RightExists
      andThen(applySubst(unionAxiom of (z -> a, x -> union(r))))
    }
    val unionB = have(in(unorderedPair(a, b), union(r)) |- in(b, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(b, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, secondElemInPair of (x -> a, y -> b))
      thenHave(in(unorderedPair(a, b), union(r)) |- ∃(y, in(b, y) /\ in(y, union(r)))) by RightExists
      andThen(applySubst(unionAxiom of (z -> b, x -> union(r))))
    }

    have(thesis) by Tautology.from(unionUP, unionA, unionB)
  }

  /**
   * Binary Relation --- A binary relation `r` from `a` to `b` is a subset of
   * the [[cartesianProduct]] of `a` and `b`, `a * b`. We say `x r y`, `r(x,
   * y)`, or `r relates x to y` for `(x, y) ∈ r`.
   */
  val relationBetween = DEF(r, a, b) --> subset(r, cartesianProduct(a, b))

  /**
   * `r` is a relation *from* `a` if there exists a set `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relationFrom = DEF(r, a) --> ∃(b, relationBetween(r, a, b))

  /**
   * `r` is a relation if there exist sets `a` and `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relation = DEF(r) --> ∃(a, ∃(b, relationBetween(r, a, b)))

  val relationDomainUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> ∃(a, in(pair(t, a), r))))
  ) {
    val uniq = have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))))) by UniqueComprehension(
      union(union(r)),
      lambda(Seq(t, b), ∃(a, in(pair(t, a), r)))
    )

    // eliminating t \in UU r
    // since it is implied by the second condition
    val transform = have(∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) subproof {
      val hypo = have(in(pair(t, a), r) |- in(pair(t, a), r)) by Hypothesis
      have(in(pair(t, a), r) |- in(t, union(union(r))) /\ in(a, union(union(r)))) by Cut(hypo, pairInSetImpliesPairInUnion of (a -> t, b -> a))
      thenHave(in(pair(t, a), r) |- in(t, union(union(r)))) by Weakening
      thenHave(∃(a, in(pair(t, a), r)) |- in(t, union(union(r)))) by LeftExists
      val lhs = thenHave(∃(a, in(pair(t, a), r)) ==> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) by Tautology
      val rhs = have((∃(a, in(pair(t, a), r)) /\ in(t, union(union(r)))) ==> ∃(a, in(pair(t, a), r))) by Restate

      val subst = have(∃(a, in(pair(t, a), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) by RightIff(lhs, rhs)

      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) by Hypothesis
      val cutRhs = thenHave(
        (in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))), ∃(a, in(pair(t, a), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (∃(
          a,
          in(pair(t, a), r)
        ))
      ) by RightSubstIff(List((∃(a, in(pair(t, a), r)), in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))), lambda(h, in(t, z) <=> h))
      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (∃(a, in(pair(t, a), r)))) by Cut(subst, cutRhs)
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (∃(a, in(pair(t, a), r)))) by LeftForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r))))) by RightForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by RightExists
      thenHave(thesis) by LeftExists
    }

    // converting the exists to existsOne
    val cutL = have(
      ∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))))
    ) by Restate.from(existsOneImpliesExists of (P -> lambda(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))))))
    val cutR = have(∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by Restate.from(
      uniqueByExtension of (schemPred -> lambda(t, (∃(a, in(pair(t, a), r)))))
    )

    val trL =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by Cut(cutL, transform)
    val trR =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by Cut(trL, cutR)

    have(thesis) by Cut.withParameters(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))))(uniq, trR)
  }

  /**
   * (Binary) Relation Domain --- The set containing the first elements of every
   * pair in a relation `r`. Alternatively, the set of elements which are
   * related to another element by `r`.
   *
   *      `dom(r) = {z ∈ ∪ ∪ r | ∃ t. (z, t) ∈ r}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * The first part is proved redundant by [[pairInSetImpliesPairInUnion]].
   * We have,
   *
   *      `dom(r) = {z | ∃ t. (z, t) ∈ r}`
   *
   * @param r relation (set)
   */
  val relationDomain = DEF(r) --> The(z, ∀(t, in(t, z) <=> ∃(a, in(pair(t, a), r))))(relationDomainUniqueness)

  val relationRangeUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> ∃(a, in(pair(a, t), r))))
  ) {
    val uniq = have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))))) by UniqueComprehension(
      union(union(r)),
      lambda(Seq(t, b), ∃(a, in(pair(a, t), r)))
    )

    // eliminating t \in UU r
    // since it is implied by the second condition
    val transform = have(∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) subproof {
      val hypo = have(in(pair(a, t), r) |- in(pair(a, t), r)) by Hypothesis
      have(in(pair(a, t), r) |- in(t, union(union(r))) /\ in(a, union(union(r)))) by Cut(hypo, pairInSetImpliesPairInUnion of (a -> a, b -> t))
      thenHave(in(pair(a, t), r) |- in(t, union(union(r)))) by Weakening
      thenHave(∃(a, in(pair(a, t), r)) |- in(t, union(union(r)))) by LeftExists
      val lhs = thenHave(∃(a, in(pair(a, t), r)) ==> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) by Tautology
      val rhs = have((∃(a, in(pair(a, t), r)) /\ in(t, union(union(r)))) ==> ∃(a, in(pair(a, t), r))) by Restate

      val subst = have(∃(a, in(pair(a, t), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) by RightIff(lhs, rhs)

      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) by Hypothesis
      val cutRhs = thenHave(
        (in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))), ∃(a, in(pair(a, t), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (∃(
          a,
          in(pair(a, t), r)
        ))
      ) by RightSubstIff(List((∃(a, in(pair(a, t), r)), in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))), lambda(h, in(t, z) <=> h))
      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (∃(a, in(pair(a, t), r)))) by Cut(subst, cutRhs)
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (∃(a, in(pair(a, t), r)))) by LeftForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r))))) by RightForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by RightExists
      thenHave(thesis) by LeftExists
    }

    // converting the exists to existsOne
    val cutL = have(
      ∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))))
    ) by Restate.from(existsOneImpliesExists of (P -> lambda(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))))))
    val cutR = have(∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by Restate.from(
      uniqueByExtension of (schemPred -> lambda(t, (∃(a, in(pair(a, t), r)))))
    )

    val trL =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by Cut(cutL, transform)
    val trR =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by Cut(trL, cutR)

    have(thesis) by Cut.withParameters(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))))(uniq, trR)
  }

  /**
   * (Binary) Relation Range --- The set containing the second elements of every
   * pair in a relation `r`. Alternatively, the set of elements which another
   * element relates to by `r`.
   *
   *      `range(r) = {z ∈ ∪ ∪ r | ∃ t. (t, z) ∈ r}
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * The first part is proved redundant by [[pairInSetImpliesPairInUnion]].
   * We have,
   *
   *      `range(r) = {z | ∃ t. (t, z) ∈ r}`
   *
   * @param r relation (set)
   */
  val relationRange = DEF(r) --> The(z, ∀(t, in(t, z) <=> ∃(a, in(pair(a, t), r))))(relationRangeUniqueness)

  /**
   * (Binary) Relation Field --- The union of the domain and range of a
   * relation, or the set of all elements related by `r`.
   *
   * @param r relation (set)
   */
  val relationField = DEF(r) --> (setUnion(relationDomain(r), relationRange(r)))

  /**
   * Theorem --- the union of two relations is a relation, with domains and codomains
   * unions of the constituents.
   *
   * Effectively,
   *
   *    `f ⊆ a * b; g ⊆ c * d ⊢ (f ∪ g) ⊆ (a ∪ c) * (b ∪ d)`
   */
  val unionOfTwoRelationsWithField = Theorem(
    relationBetween(f, a, b) /\ relationBetween(g, c, d) |- relationBetween(setUnion(f, g), setUnion(a, c), setUnion(b, d))
  ) {
    val fab = have(relationBetween(f, a, b) <=> subset(f, cartesianProduct(a, b))) by Restate.from(relationBetween.definition of r -> f)
    val gcd = fab of (f -> g, a -> c, b -> d)
    val fug = fab of (f -> setUnion(f, g), a -> setUnion(a, c), b -> setUnion(b, d))

    have(subset(f, cartesianProduct(a, b)) /\ subset(g, cartesianProduct(c, d)) |- subset(setUnion(f, g), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Tautology.from(
      unionOfCartesianProducts,
      unionOfSubsetsOfDifferentSets of (a -> f, b -> g, c -> cartesianProduct(a, b), d -> cartesianProduct(c, d)),
      subsetTransitivity of (a -> setUnion(f, g), b -> setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), c -> cartesianProduct(setUnion(a, c), setUnion(b, d)))
    )

    have(thesis) by Tautology.from(lastStep, fab, gcd, fug)
  }

  /**
   * Theorem --- the union of two relations is a relation. (weaker form)
   *
   * Weakening of [[unionOfTwoRelationsWithField]] to unknown fields.
   */
  val unionOfTwoRelations = Theorem(
    relation(f) /\ relation(g) |- relation(setUnion(f, g))
  ) {
    val relf = have(relation(f) <=> exists(x, exists(y, relationBetween(f, x, y)))) by Restate.from(relation.definition of r -> f)
    val relg = relf of f -> g
    val relfug = relf of f -> setUnion(f, g)

    have((relationBetween(f, a, b), relationBetween(g, c, d)) |- relationBetween(setUnion(f, g), setUnion(a, c), setUnion(b, d))) by Restate.from(unionOfTwoRelationsWithField)
    thenHave((relationBetween(f, a, b), relationBetween(g, c, d)) |- exists(y, relationBetween(setUnion(f, g), setUnion(a, c), y))) by RightExists
    thenHave((relationBetween(f, a, b), relationBetween(g, c, d)) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by RightExists
    thenHave((relationBetween(f, a, b), exists(d, relationBetween(g, c, d))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists
    thenHave((relationBetween(f, a, b), exists(c, exists(d, relationBetween(g, c, d)))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists
    thenHave((exists(b, relationBetween(f, a, b)), exists(c, exists(d, relationBetween(g, c, d)))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists
    thenHave((exists(a, exists(b, relationBetween(f, a, b))), exists(c, exists(d, relationBetween(g, c, d)))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists

    thenHave((relation(f), relation(g)) |- relation(setUnion(f, g))) by Substitution.apply2(true, relf, relg, relfug)
  }

  /**
   * Functional --- A binary [[relation]] is functional if it maps every element in its domain
   * to a unique element (in its range).
   *
   *     `functional(f) ⇔ relation(f) ∧ ∀ x. (∃ y. (x, y) ∈ f) ⟹ (∃! y. (x, y) ∈ f)`
   *
   * We may alternatively denote `(z, y) ∈ f` as `y = f(z)`.
   *
   * @param f relation (set)
   */
  val functional = DEF(f) --> relation(f) /\ ∀(x, ∃(y, in(pair(x, y), f)) ==> ∃!(y, in(pair(x, y), f)))

  /**
   * Functional Over a Set --- A binary [[relation]] is functional over a set `x` if it is
   * [[functional]] and has`x` as its domain ([[relationDomain]]).
   *
   * @param f relation (set)
   * @param x set
   */
  val functionalOver = DEF(f, x) --> functional(f) /\ (relationDomain(f) === x)

  val setOfFunctionsUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))
  ) {
    have(thesis) by UniqueComprehension(powerSet(cartesianProduct(x, y)), lambda(Seq(t, z), functionalOver(t, x)))
  }

  /**
   * Set of functions --- All functions from `x` to `y`, denoted `x → y` or
   * `→(x, y)`.
   *
   * Since functions from `x` to `y` contain pairs of the form `(a, b) | a ∈
   * x, b ∈ y`, it is a filtering on the power set of their product, i.e. `x
   * → y ⊆ PP(x * y)`.
   */
  val setOfFunctions = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))(setOfFunctionsUniqueness)

  /**
   * Function From (x to y) --- denoted  `f ∈ x → y` or `f: x → y`.
   */
  val functionFrom = DEF(f, x, y) --> in(f, setOfFunctions(x, y))

  /**
   * Theorem --- A function between two sets is [[functional]]
   */
  val functionFromImpliesFunctional = Theorem(
    functionFrom(f, x, y) |- functional(f)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    val funOver = have(functionFrom(f, x, y) |- functional(f)) by Tautology.from(funSetDef, functionFrom.definition, functionalOver.definition)
  }

  val functionApplicationUniqueness = Theorem(
    ∃!(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))
  ) {
    val prem = functional(f) /\ in(x, relationDomain(f))

    // we prove thesis by two cases, first by assuming prem, and then by assuming !prem

    // positive direction
    have(functional(f) |- ∀(x, ∃(y, in(pair(x, y), f)) ==> ∃!(y, in(pair(x, y), f)))) by Tautology.from(functional.definition)
    val funcDef = thenHave(functional(f) |- ∃(y, in(pair(x, y), f)) ==> ∃!(y, in(pair(x, y), f))) by InstantiateForall(x)

    have((relationDomain(f) === relationDomain(f)) <=> ∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by InstantiateForall(relationDomain(f))(
      relationDomain.definition of (r -> f)
    )
    thenHave(∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by Restate
    thenHave(in(x, relationDomain(f)) <=> (∃(y, in(pair(x, y), f)))) by InstantiateForall(x)
    val domDef = thenHave(in(x, relationDomain(f)) |- ∃(y, in(pair(x, y), f))) by Weakening

    val uniqPrem = have(functional(f) /\ in(x, relationDomain(f)) |- ∃!(z, in(pair(x, z), f))) by Tautology.from(funcDef, domDef)

    val positive = have(prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ ⊤))) subproof {
        val iff = have(prem |- (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) by Restate
        have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> in(pair(x, y), f))) by Restate
        val subst = thenHave((prem /\ ((z === y) <=> in(pair(x, y), f)), (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by RightSubstIff(
          List(((in(pair(x, y), f)), (prem ==> in(pair(x, y), f)))),
          lambda(h, ((z === y) <=> h))
        )

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(prem |- (!prem ==> (y === ∅)) <=> ⊤) by Restate
        val topSubst = have(
          (prem /\ ((z === y) <=> in(pair(x, y), f)), ((!prem ==> (y === ∅)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff(List(((!prem ==> (y === ∅)), ⊤)), lambda(h, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ h))))(lhs)

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification = have((prem, ∃!(z, in(pair(x, z), f))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
        have((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅)))))) by RightForall
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
        thenHave(
          (prem, ∃(z, ∀(y, ((z === y) <=> in(pair(x, y), f))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
        ) by LeftExists
        thenHave(thesis) by Restate
      }

      have(thesis) by Cut(uniqPrem, quantification)
    }

    // negative
    have((∅ === y) <=> (∅ === y)) by Restate
    thenHave(∀(y, (∅ === y) <=> (∅ === y))) by RightForall
    thenHave(∃(z, ∀(y, (z === y) <=> (∅ === y)))) by RightExists
    val emptyPrem = thenHave(∃!(z, (z === ∅))) by Restate

    val negative = have(!prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> ((!prem ==> (y === ∅)) /\ ⊤))) subproof {
        val iff = have(!prem |- ((y === ∅)) <=> (!prem ==> (y === ∅))) by Restate
        have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> (y === ∅))) by Restate
        val subst = thenHave(
          (!prem /\ ((z === y) <=> (y === ∅)), ((y === ∅)) <=> (!prem ==> (y === ∅))) |- ((z === y) <=> (!prem ==> (y === ∅)))
        ) by RightSubstIff(List((((y === ∅)), (!prem ==> (y === ∅)))), lambda(h, ((z === y) <=> h)))

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> (!prem ==> (y === ∅)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(!prem |- (prem ==> in(pair(x, y), f)) <=> ⊤) by Restate
        val topSubst = have(
          (!prem /\ ((z === y) <=> (y === ∅)), ((prem ==> in(pair(x, y), f)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff(List(((prem ==> in(pair(x, y), f)), ⊤)), lambda(h, ((z === y) <=> ((!prem ==> (y === ∅)) /\ h))))(lhs)

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification =
        have((!prem, ∃!(z, (z === ∅))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
          have((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∀(y, (z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by RightForall
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
          thenHave(
            (!prem, ∃(z, ∀(y, ((z === y) <=> (y === ∅))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
          ) by LeftExists
          thenHave(thesis) by Restate
        }

      have(thesis) by Cut(emptyPrem, quantification)
    }

    val negRhs = thenHave(() |- (prem, ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅)))))) by Restate

    have(thesis) by Cut.withParameters(prem)(negRhs, positive)
  }

  /**
   * Function application --- denoted `f(x)`. The unique element `z` such that
   * `(x, z) ∈ f` if it exists and `f` is functional, [[emptySet]] otherwise.
   */
  val app =
    DEF(f, x) --> The(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))(functionApplicationUniqueness)

  /**
   * Surjective (function) --- a function `f: x → y` is surjective iff it
   * maps to every `b ∈ y` from atleast one `a ∈ x`.
   *
   * `surjective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b)`
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))

  /**
   * Alias for [[surjective]]
   */
  val onto = surjective

  /**
   * Injective (function) --- a function `f: x → y` is injective iff it maps
   * to every `b ∈ y` from atmost one `a ∈ x`.
   *
   * `injective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b) ⟹ (∃! a ∈ x. f(a) = b)`
   */
  val injective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> (∃(a, in(a, x) /\ in(pair(a, b), f)) ==> ∃!(a, in(a, x) /\ in(pair(a, b), f))))

  /**
   * Alias for [[injective]]
   */
  val oneone = injective

  /**
   * Bijective function --- a function `f: x → y` is bijective iff it is
   * [[injective]] and [[surjective]].
   */
  val bijective = DEF(f, x, y) --> injective(f, x, y) /\ surjective(f, x, y)

  /**
   * Invertible Function --- a function from `x` to `y` is invertible iff it is
   * [[bijective]]. See also, [[inverseFunction]]
   */
  val invertibleFunction = DEF(f, x, y) --> bijective(f, x, y)

  /**
   * Inverse Function --- the inverse of a function `f: x → y`, denoted
   * `f^-1`, is a function from `y` to `x` such that `∀ a ∈ x, b ∈ y.
   * f(f^-1(b)) = b ∧ f^-1(f(b)) = b`.
   */
  val inverseFunctionOf = DEF(g, f, x, y) --> functionFrom(g, y, x) /\ functionFrom(f, x, y) /\ ∀(a, (in(a, y) ==> (a === app(f, app(g, a)))) /\ (in(a, x) ==> (a === app(g, app(f, a)))))

  // val inverseFunctionExistsIfInvertible = makeTHM(
  //    invertibleFunction(f, x, y) <=> ∃(g, inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunctionIsUniqueIfItExists = makeTHM(
  //   ∃(g, inverseFunctionOf(g, f, x, y)) |- ∃!(g, inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunctionUniqueness = makeTHM(
  //    ∃!(g, invertibleFunction(f) ==> inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunction = DEF (f, x, y) --> The(g, invertibleFunction(f) ==> inverseFunctionOf(g, f, x, y))(inverseFunctionUniqueness)

  val restrictedFunctionUniqueness = Theorem(
    ∃!(g, ∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))
  ) {
    have(∃!(g, ∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))) by UniqueComprehension(
      f,
      lambda(Seq(t, b), ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))
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
  val restrictedFunction = DEF(f, x) --> The(g, ∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))(restrictedFunctionUniqueness)

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

  val piUniqueness = Theorem(
    ∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))
  ) {
    have(∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))) by UniqueComprehension(
      powerSet(Sigma(x, f)),
      lambda(Seq(z, y), (subset(x, relationDomain(z)) /\ functional(z)))
    )
  }

  /**
   * Dependent Product (Pi)
   *
   * TODO: explain
   */
  val Pi = DEF(x, f) --> The(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))(piUniqueness)

  /**
   * Properties of relations
   */

  /**
   * Reflexive Relation --- `∀ x. x R x`
   */
  val reflexive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, in(y, x) ==> in(pair(y, y), r))

  /**
   * Symmetric Relation --- `∀ x y. x R y ⇔ y R x`
   */
  val symmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, in(pair(y, z), r) <=> in(pair(z, y), r)))

  /**
   * Transitive Relation --- `∀ x y z. x R y ∧ y R z ⇒ x R z`
   */
  val transitive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(w, ∀(y, ∀(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))))

  /**
   * Equivalence Relation --- A relation is an equivalence relation if it is
   * [[reflexive]], [[symmetric]], and [[transitive]].
   */
  val equivalence = DEF(r, x) --> reflexive(r, x) /\ symmetric(r, x) /\ transitive(r, x)

  /**
   * Anti-reflexive Relation --- `∀ x. ! x R x`
   */
  val antiReflexive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, in(y, x) ==> !in(pair(y, y), r))

  /**
   * Irreflexive Relation --- Alias for [[antiReflexive]].
   */
  val irreflexive = antiReflexive

  /**
   * Anti-symmetric Relation --- `∀ x y. x R y ∧ y R x ⇒ y = x`
   */
  val antiSymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))

  /**
   * Asymmetric Relation --- `∀ x y. x R y ⇔ ! y R x`
   */
  val asymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))

  /**
   * Connected Relation --- `∀ x y. (x R y) ∨ (y R x) ∨ (y = x)`
   */
  val connected = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z))))

  /**
   * Total Relation --- Alias for [[connected]].
   */
  val total = connected

  /**
   * Strongly Connected Relation ---
   *     `∀ x y z. y R x ∧ z R x ⇒ y R z ∨ z R y`
   */
  val stronglyConnected = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r))))

  /**
   * Theorem --- the empty set is a relation, the empty relation, between any two sets.
   */
  val emptySetRelation = Lemma(
    () |- relationBetween(emptySet(), a, b)
  ) {
    have(thesis) by Tautology.from(emptySetIsASubset of (x -> cartesianProduct(a, b)), relationBetween.definition of (r -> emptySet()))
  }

  /**
   * Theorem --- the empty relation is a relation on the empty set.
   */
  val emptySetRelationOnItself = Lemma(
    () |- relationBetween(emptySet(), emptySet(), emptySet())
  ) {
    have(thesis) by Restate.from(emptySetRelation of (a -> emptySet(), b -> emptySet()))
  }

  /**
   * Theorem --- empty relation on the empty set is reflexive.
   */
  val emptyRelationReflexiveOnItself = Lemma(
    () |- reflexive(emptySet(), emptySet())
  ) {
    have(() |- in(y, emptySet()) ==> in(pair(y, y), emptySet())) by Tautology.from(emptySetAxiom of (x -> y))
    val refCond = thenHave(() |- forall(y, in(y, emptySet()) ==> in(pair(y, y), emptySet()))) by RightForall

    have(thesis) by Tautology.from(reflexive.definition of (r -> emptySet(), x -> emptySet()), emptySetRelationOnItself, refCond)
  }

  /**
   * Theorem --- the empty relation is symmetric.
   */
  val emptyRelationSymmetric = Lemma(
    () |- symmetric(emptySet(), a)
  ) {
    have(() |- in(pair(y, z), emptySet()) <=> in(pair(z, y), emptySet())) by Tautology.from(emptySetAxiom of (x -> pair(y, z)), emptySetAxiom of (x -> pair(z, y)))
    thenHave(() |- forall(z, in(pair(y, z), emptySet()) <=> in(pair(z, y), emptySet()))) by RightForall
    val symCond = thenHave(() |- forall(y, forall(z, in(pair(y, z), emptySet()) <=> in(pair(z, y), emptySet())))) by RightForall

    have(thesis) by Tautology.from(symmetric.definition of (r -> emptySet(), x -> a), emptySetRelation of (b -> a), symCond)
  }

  /**
   * Theorem --- the empty relation is irreflexive.
   */
  val emptyRelationIrreflexive = Lemma(
    () |- irreflexive(emptySet(), a)
  ) {
    have(() |- in(y, a) ==> !in(pair(y, y), emptySet())) by Tautology.from(emptySetAxiom of (x -> pair(y, y)))
    val irrefCond = thenHave(() |- forall(y, in(y, a) ==> !in(pair(y, y), emptySet()))) by RightForall

    have(thesis) by Tautology.from(irreflexive.definition of (r -> emptySet(), x -> a), emptySetRelation of (b -> a), irrefCond)
  }

  /**
   * Theorem --- the empty relation is transitive.
   */
  val emptyRelationTransitive = Lemma(
    () |- transitive(emptySet(), a)
  ) {
    have(() |- (in(pair(w, y), emptySet()) /\ in(pair(y, z), emptySet())) ==> in(pair(w, z), emptySet())) by Tautology.from(emptySetAxiom of (x -> pair(w, y)))
    thenHave(() |- forall(z, (in(pair(w, y), emptySet()) /\ in(pair(y, z), emptySet())) ==> in(pair(w, z), emptySet()))) by RightForall
    thenHave(() |- forall(y, forall(z, (in(pair(w, y), emptySet()) /\ in(pair(y, z), emptySet())) ==> in(pair(w, z), emptySet())))) by RightForall
    val trsCond = thenHave(() |- forall(w, forall(y, forall(z, (in(pair(w, y), emptySet()) /\ in(pair(y, z), emptySet())) ==> in(pair(w, z), emptySet()))))) by RightForall

    have(thesis) by Tautology.from(transitive.definition of (r -> emptySet(), x -> a), emptySetRelation of (b -> a), trsCond)
  }

  /**
   * Theorem --- the empty relation is an equivalence relation on the empty set.
   */
  val emptyRelationEquivalence = Lemma(
    () |- equivalence(emptySet(), emptySet())
  ) {
    have(thesis) by Tautology.from(
      equivalence.definition of (r -> emptySet(), x -> emptySet()),
      emptyRelationReflexiveOnItself,
      emptyRelationSymmetric of (a -> emptySet()),
      emptyRelationTransitive of (a -> emptySet())
    )
  }

  /**
   * Theorem --- the empty relation is anti-symmetric.
   */
  val emptyRelationAntiSymmetric = Lemma(
    () |- antiSymmetric(emptySet(), a)
  ) {
    have(() |- (in(pair(y, z), emptySet()) /\ in(pair(z, y), emptySet())) ==> (y === z)) by Tautology.from(emptySetAxiom of (x -> pair(y, z)))
    thenHave(() |- forall(z, (in(pair(y, z), emptySet()) /\ in(pair(z, y), emptySet())) ==> (y === z))) by RightForall
    val ansymCond = thenHave(() |- forall(y, forall(z, (in(pair(y, z), emptySet()) /\ in(pair(z, y), emptySet())) ==> (y === z)))) by RightForall

    have(thesis) by Tautology.from(antiSymmetric.definition of (r -> emptySet(), x -> a), emptySetRelation of (b -> a), ansymCond)
  }

  /**
   * Theorem --- the empty relation is asymmetric.
   */
  val emptyRelationAsymmetric = Lemma(
    () |- asymmetric(emptySet(), a)
  ) {
    have(() |- in(pair(y, z), emptySet()) ==> !in(pair(z, y), emptySet())) by Tautology.from(emptySetAxiom of (x -> pair(y, z)))
    thenHave(() |- forall(z, in(pair(y, z), emptySet()) ==> !in(pair(z, y), emptySet()))) by RightForall
    val asymCond = thenHave(() |- forall(y, forall(z, in(pair(y, z), emptySet()) ==> !in(pair(z, y), emptySet())))) by RightForall

    have(thesis) by Tautology.from(asymmetric.definition of (r -> emptySet(), x -> a), emptySetRelation of (b -> a), asymCond)
  }

  /**
   * Theorem --- the empty relation is total on the empty set.
   */
  val emptyRelationTotalOnItself = Lemma(
    () |- total(emptySet(), emptySet())
  ) {
    have((in(y, emptySet()) /\ in(z, emptySet())) ==> (in(pair(y, z), emptySet()) \/ in(pair(z, y), emptySet()) \/ (y === z))) by Tautology.from(emptySetAxiom of x -> y)
    thenHave(forall(z, (in(y, emptySet()) /\ in(z, emptySet())) ==> (in(pair(y, z), emptySet()) \/ in(pair(z, y), emptySet()) \/ (y === z)))) by RightForall
    thenHave(forall(y, forall(z, (in(y, emptySet()) /\ in(z, emptySet())) ==> (in(pair(y, z), emptySet()) \/ in(pair(z, y), emptySet()) \/ (y === z))))) by RightForall

    have(thesis) by Tautology.from(lastStep, total.definition of (r -> emptySet(), x -> emptySet()), emptySetRelationOnItself)
  }

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
  val subsetReflexivity = Theorem(
    subset(x, x)
  ) {
    val subdef = have(subset(x, x) <=> ∀(z, ⊤)) by Restate.from(subsetAxiom of (y -> x))
    andThen(applySubst(closedFormulaUniversal of (VariableFormulaLabel("p") -> ⊤)))

    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Symmetry of Equality and Subset
   *
   * [[equality]] implies a [[subset]] ordering, and [[subset]] ordering in both
   * directions implies [[equality]].
   */
  val subsetEqualitySymmetry = Theorem(
    (x === y) <=> (subset(x, y) /\ subset(y, x))
  ) {
    have(subset(x, y) /\ subset(y, x) <=> subset(x, y) /\ subset(y, x)) by Restate
    thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ subset(y, x)) by Substitution.apply2(false, subsetAxiom)
    thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ forall(t, in(t, y) ==> in(t, x))) by Substitution.apply2(false, subsetAxiom of (x -> y, y -> x))
    andThen(applySubst(universalConjunctionCommutation of (P -> lambda(t, in(t, x) ==> in(t, y)), Q -> lambda(t, in(t, y) ==> in(t, x)))))
    andThen(applySubst(extensionalityAxiom))
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- if `f` is [[functional]] over `x`, then `x` is precisely its
   * domain as a relation.
   */
  val functionalOverImpliesDomain = Theorem(
    functionalOver(f, x) |- (relationDomain(f) === x)
  ) {
    have(thesis) by Tautology.from(functionalOver.definition)
  }

  /**
   * Theorem --- if `f` is a [[functionFrom]] `x` to `y`, i.e. `f ∈ x → y`,
   * then `x` is precisely its domain as a relation.
   */
  val functionFromImpliesDomainEq = Theorem(
    functionFrom(f, x, y) |- (relationDomain(f) === x)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(thesis) by Tautology.from(functionFrom.definition, funSetDef, functionalOver.definition)
  }

  /**
   * Theorem --- the range of a function is a subset of its codomain.
   */
  val functionImpliesRangeSubsetOfCodomain = Theorem(
    functionFrom(f, x, y) |- subset(relationRange(f), y)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(functionFrom(f, x, y) |- ∀(z, in(z, f) ==> in(z, cartesianProduct(x, y)))) by Tautology.from(
      functionFrom.definition,
      funSetDef,
      powerAxiom of (x -> f, y -> cartesianProduct(x, y)),
      subsetAxiom of (x -> f, y -> cartesianProduct(x, y))
    )
    thenHave(functionFrom(f, x, y) |- in(pair(a, t), f) ==> in(pair(a, t), cartesianProduct(x, y))) by InstantiateForall(pair(a, t))
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(pair(a, t), cartesianProduct(x, y))) by Restate
    andThen(applySubst(pairInCartesianProduct of (b -> t)))
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(t, y)) by Weakening
    val funFromty = thenHave((functionFrom(f, x, y), ∃(a, in(pair(a, t), f))) |- in(t, y)) by LeftExists

    have(∀(t, in(t, relationRange(f)) <=> (∃(a, in(pair(a, t), f))))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    thenHave(in(t, relationRange(f)) <=> (∃(a, in(pair(a, t), f)))) by InstantiateForall(t)
    val ranat = thenHave(in(t, relationRange(f)) |- ∃(a, in(pair(a, t), f))) by Weakening

    have((functionFrom(f, x, y), in(t, relationRange(f))) |- in(t, y)) by Cut(ranat, funFromty)
    thenHave((functionFrom(f, x, y)) |- in(t, relationRange(f)) ==> in(t, y)) by Restate
    thenHave((functionFrom(f, x, y)) |- ∀(t, in(t, relationRange(f)) ==> in(t, y))) by RightForall
    andThen(applySubst(subsetAxiom of (x -> relationRange(f))))
  }

  /**
   * Theorem --- if a set is in the range of a function, then there exists atleast
   * one element in the domain mapping to it.
   */
  val inRangeImpliesPullbackExists = Theorem(
    functional(f) /\ in(z, relationRange(f)) |- ∃(t, in(t, relationDomain(f)) /\ (app(f, t) === z))
  ) {
    val appIff = have(
      (z === app(f, t)) <=> ((functional(f) /\ in(t, relationDomain(f))) ==> in(pair(t, z), f)) /\ ((!functional(f) \/ !in(t, relationDomain(f))) ==> (z === ∅))
    ) by InstantiateForall(z)(app.definition of (x -> t))

    have(∀(t, in(t, relationRange(f)) <=> ∃(a, in(pair(a, t), f)))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    thenHave(in(z, relationRange(f)) <=> ∃(a, in(pair(a, z), f))) by InstantiateForall(z)
    val elementInDomainExists = thenHave(in(z, relationRange(f)) |- ∃(t, in(pair(t, z), f))) by Weakening

    val toApp = have(
      (functional(f), in(t, relationDomain(f)), in(pair(t, z), f)) |- ((functional(f) /\ in(t, relationDomain(f))) ==> in(pair(t, z), f)) /\ ((!functional(f) \/ !in(
        t,
        relationDomain(f)
      )) ==> (z === ∅))
    ) by Restate
    val zAppdom = have((functional(f), in(t, relationDomain(f)), in(pair(t, z), f)) |- (z === app(f, t))) by Tautology.from(toApp, appIff)

    val pairInDomain = have(in(pair(t, z), f) |- in(t, relationDomain(f))) subproof {
      have(∀(t, in(t, relationDomain(f)) <=> ∃(a, in(pair(t, a), f)))) by InstantiateForall(relationDomain(f))(relationDomain.definition of (r -> f))
      val domDef = thenHave(in(t, relationDomain(f)) <=> ∃(a, in(pair(t, a), f))) by InstantiateForall(t)

      have(in(pair(t, z), f) |- in(pair(t, z), f)) by Hypothesis
      val pairEx = thenHave(in(pair(t, z), f) |- ∃(a, in(pair(t, a), f))) by RightExists

      have(thesis) by Tautology.from(domDef, pairEx)
    }

    val zApp2 = have((functional(f), in(pair(t, z), f)) |- (z === app(f, t))) by Cut(pairInDomain, zAppdom)
    have((functional(f), in(pair(t, z), f)) |- in(t, relationDomain(f)) /\ (z === app(f, t))) by RightAnd(pairInDomain, zApp2)
    thenHave((functional(f), in(pair(t, z), f)) |- ∃(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by RightExists
    val zAppIfExists = thenHave((functional(f), ∃(t, in(pair(t, z), f))) |- ∃(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by LeftExists

    have((functional(f), in(z, relationRange(f))) |- ∃(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by Cut(elementInDomainExists, zAppIfExists)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- if a function is [[surjective]], its range is equal to its codomain.
   */
  val surjectiveImpliesRangeIsCodomain = Theorem(
    surjective(f, x, y) |- (y === relationRange(f))
  ) {
    have(surjective(f, x, y) |- ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))) by Tautology.from(surjective.definition)
    val surjDef = thenHave(surjective(f, x, y) |- in(b, y) ==> ∃(a, in(pair(a, b), f))) by InstantiateForall(b)
    have(∀(t, in(t, relationRange(f)) <=> (∃(a, in(pair(a, t), f))))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    val rangeDef = thenHave(in(b, relationRange(f)) <=> (∃(a, in(pair(a, b), f)))) by InstantiateForall(b)

    have(surjective(f, x, y) |- in(b, y) ==> in(b, relationRange(f))) by Tautology.from(surjDef, rangeDef)
    thenHave(surjective(f, x, y) |- ∀(b, in(b, y) ==> in(b, relationRange(f)))) by RightForall
    val surjsub = andThen(applySubst(subsetAxiom of (x -> y, y -> relationRange(f))))

    have((surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, relationRange(f)) /\ subset(relationRange(f), y)) by RightAnd(surjsub, functionImpliesRangeSubsetOfCodomain)
    val funceq = andThen(applySubst(subsetEqualitySymmetry of (x -> y, y -> relationRange(f))))

    val surjfunc = have(surjective(f, x, y) |- functionFrom(f, x, y)) by Tautology.from(surjective.definition)

    have(thesis) by Cut(surjfunc, funceq)
  }

  /**
   * Theorem --- Cantor's Theorem
   *
   * There is no [[surjective]] mapping ([[functionFrom]]) a set to its [[powerSet]].
   *
   * In terms of cardinality, it asserts that a set is strictly smaller than
   * its power set.
   */
  val cantorTheorem = Theorem(
    surjective(f, x, powerSet(x)) |- ()
  ) {
    // define y = {z \in x | ! z \in f(z)}
    val ydef = ∀(t, in(t, y) <=> (in(t, x) /\ !in(t, app(f, t))))

    // y \subseteq x
    // y \in P(x)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(t, y) <=> (in(t, x) /\ !in(t, app(f, t)))) by InstantiateForall(t)
    thenHave(ydef |- in(t, y) ==> in(t, x)) by Weakening
    thenHave(ydef |- ∀(t, in(t, y) ==> in(t, x))) by RightForall
    andThen(applySubst(subsetAxiom of (x -> y, y -> x)))
    andThen(applySubst(powerAxiom of (x -> y, y -> x)))
    val yInPower = thenHave(ydef |- in(y, powerSet(x))) by Restate

    // y \in range(f)
    have(surjective(f, x, powerSet(x)) |- (powerSet(x) === relationRange(f))) by Restate.from(surjectiveImpliesRangeIsCodomain of (y -> powerSet(x)))
    andThen(applySubst(extensionalityAxiom of (x -> powerSet(x), y -> relationRange(f))))
    val surjRange = thenHave(surjective(f, x, powerSet(x)) |- in(y, powerSet(x)) <=> in(y, relationRange(f))) by InstantiateForall(y)
    val yInRange = have((ydef, surjective(f, x, powerSet(x))) |- in(y, relationRange(f))) by Tautology.from(yInPower, surjRange)

    // \exists z. z \in x /\ f(z) = y
    val surjToFunFrom = have(surjective(f, x, powerSet(x)) |- functionFrom(f, x, powerSet(x))) by Tautology.from(surjective.definition of (y -> powerSet(x)))
    val existsZdom = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, relationDomain(f)) /\ (app(f, z) === y))) by Tautology.from(
      yInRange,
      surjective.definition of (y -> powerSet(x)),
      inRangeImpliesPullbackExists of (z -> y),
      functionFromImpliesFunctional of (y -> powerSet(x))
    )
    val xeqdom = thenHave((ydef, surjective(f, x, powerSet(x)), (relationDomain(f) === x)) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by RightSubstEq(
      List((x, relationDomain(f))),
      lambda(x, ∃(z, in(z, x) /\ (app(f, z) === y)))
    )
    val existsZ = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by Tautology.from(
      surjective.definition of (y -> powerSet(x)),
      functionFromImpliesDomainEq of (y -> powerSet(x)),
      xeqdom
    )

    // z \in Y <=> z \in x /\ ! z \in f(z)
    // y = f(z) so z \in f(z) <=> ! z \in f(z)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by InstantiateForall(z)
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by Weakening
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, app(f, z)) <=> (in(z, x) /\ !in(z, app(f, z)))) by RightSubstEq(
      List((y, app(f, z))),
      lambda(y, in(z, y) <=> (in(z, x) /\ !in(z, app(f, z))))
    )
    thenHave((ydef, in(z, x) /\ (app(f, z) === y)) |- ()) by Tautology
    val existsToContra = thenHave((ydef, ∃(z, in(z, x) /\ (app(f, z) === y))) |- ()) by LeftExists

    have((ydef, surjective(f, x, powerSet(x))) |- ()) by Cut(existsZ, existsToContra)
    val yToContra = thenHave((∃(y, ydef), surjective(f, x, powerSet(x))) |- ()) by LeftExists
    val yexists = have(∃(y, ydef)) by Restate.from(comprehensionSchema of (z -> x, sPhi -> lambda(Seq(t, z), !in(t, app(f, t)))))

    have(thesis) by Cut(yexists, yToContra)
  }

  /**
   * Theorem --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val unionOfFunctionsIsAFunction = Lemma(
    functional(f) /\ functional(g) /\ forall(x, forall(y, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- functional(setUnion(f, g))
  ) {
    // some renaming for convenience
    val domF = relationDomain(f)
    val domG = relationDomain(g)

    val h = setUnion(f, g)
    val domH = setUnion(domF, domG)

    // is a relation
    val isRelation = have(functional(f) /\ functional(g) |- relation(h)) by Tautology.from(functional.definition, functional.definition of f -> g, unionOfTwoRelations)

    // has the uniqueness property
    val isFunctional = have(
      functional(f) /\ functional(g) /\ forall(x, forall(y, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- forall(
        x,
        exists(y, in(pair(x, y), h)) ==> existsOne(y, in(pair(x, y), h))
      )
    ) subproof {
      // x in domH <=> x in domF \/ x in domG
      val domHDef = have(in(x, domH) <=> (in(x, domF) \/ in(x, domG))) by Restate.from(setUnionMembership of (z -> x, x -> domF, y -> domG))

      // x in domF/G <=> exists y. xy in F/G
      have(forall(t, in(t, domF) <=> exists(y, in(pair(t, y), f)))) by InstantiateForall(domF)(relationDomain.definition of r -> f)
      val xInDomF = thenHave(in(x, domF) <=> exists(y, in(pair(x, y), f))) by InstantiateForall(x)
      val xInDomG = xInDomF of f -> g

      val xInDomFOne = have((functional(f), in(x, domF)) |- existsOne(y, in(pair(x, y), f))) subproof {
        have(functional(f) |- forall(x, exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f)))) by Weakening(functional.definition)
        thenHave(functional(f) |- exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f))) by InstantiateForall(x)

        have(thesis) by Tautology.from(lastStep, xInDomF)
      }

      // x in domH <=> exists y. xy in H OR domH = relationDomain(h)
      val domHIsDomain = have(in(x, domH) <=> exists(y, in(pair(x, y), h))) subproof {
        have(exists(y, in(pair(x, y), h)) <=> (exists(y, in(pair(x, y), f)) \/ exists(y, in(pair(x, y), g)))) subproof {
          have(in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g))) by Restate.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))
          thenHave(forall(y, in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g)))) by RightForall
          have(exists(y, in(pair(x, y), h)) <=> exists(y, in(pair(x, y), f) \/ in(pair(x, y), g))) by Tautology.from(
            lastStep,
            existentialEquivalenceDistribution of (P -> lambda(y, in(pair(x, y), h)), Q -> lambda(y, in(pair(x, y), f) \/ in(pair(x, y), g)))
          )
          // have(exists(y, in(pair(x, y), h)) <=> (exists(y, in(pair(x, y), f)) \/ exists(y, in(pair(x, y), g)))) by Tautology.from(lastStep, existentialDisjunctionCommutation of (P -> lambda(y, in(pair(x, y), f)), Q -> lambda(y, in(pair(x, y), g)))) // TODO: Possible Tautology Bug
          thenHave(exists(y, in(pair(x, y), h)) <=> (exists(y, in(pair(x, y), f)) \/ exists(y, in(pair(x, y), g)))) by Substitution.apply2(
            false,
            existentialDisjunctionCommutation of (P -> lambda(y, in(pair(x, y), f)), Q -> lambda(y, in(pair(x, y), g)))
          )
        }

        have(thesis) by Tautology.from(lastStep, domHDef, xInDomF, xInDomG)
      }

      // x in domF and x not in domG
      have(functional(f) |- forall(x, exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f)))) by Weakening(functional.definition)
      val exToExOne = thenHave((functional(f), exists(y, in(pair(x, y), f))) |- existsOne(y, in(pair(x, y), f))) by InstantiateForall(x)

      have(forall(y, !in(pair(x, y), g)) |- existsOne(y, in(pair(x, y), f)) <=> existsOne(y, in(pair(x, y), h))) subproof {
        val fwd = have(in(pair(x, y), f) |- in(pair(x, y), h)) by Tautology.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))
        val notzg = have(forall(y, !in(pair(x, y), g)) |- !in(pair(x, y), g)) by InstantiateForall
        have(in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g))) by Restate.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))

        have(forall(y, !in(pair(x, y), g)) |- in(pair(x, y), h) <=> (in(pair(x, y), f))) by Tautology.from(lastStep, notzg, fwd)
        thenHave(forall(y, !in(pair(x, y), g)) |- forall(y, in(pair(x, y), h) <=> (in(pair(x, y), f)))) by RightForall

        have(forall(y, !in(pair(x, y), g)) |- existsOne(y, in(pair(x, y), h)) <=> existsOne(y, in(pair(x, y), f))) by Tautology.from(
          lastStep,
          uniqueExistentialEquivalenceDistribution of (P -> lambda(z, in(pair(x, z), h)), Q -> lambda(z, in(pair(x, z), f)))
        )
      }

      val notInG = have((functional(f), in(x, domF), !in(x, domG)) |- existsOne(y, in(pair(x, y), h))) by Tautology.from(lastStep, xInDomFOne, xInDomG)

      // x not in domF and x in domG
      val notInF = have((functional(g), !in(x, domF), in(x, domG)) |- existsOne(y, in(pair(x, y), h))) by Substitution.apply2(false, unionCommutativity of (a -> g, b -> f))(notInG of (f -> g, g -> f))

      // x in domF and in domG
      have(
        forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- forall(
          x,
          forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))
        )
      ) by Hypothesis
      thenHave(
        forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))
      ) by InstantiateForall(x, y)
      thenHave((forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (in(pair(x, y), f) <=> in(pair(x, y), g))) by Restate
      val FToFG = thenHave(
        (forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (in(pair(x, y), f) <=> (in(pair(x, y), g) \/ in(pair(x, y), f)))
      ) by Tautology

      have(in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g))) by Restate.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))

      have((forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (in(pair(x, y), f) <=> in(pair(x, y), h))) by Tautology.from(
        lastStep,
        FToFG
      )
      thenHave(
        (forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- forall(y, in(pair(x, y), f) <=> in(pair(x, y), h))
      ) by RightForall
      have(
        (forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (existsOne(y, in(pair(x, y), f)) <=> existsOne(
          y,
          in(pair(x, y), h)
        ))
      ) by Tautology.from(lastStep, uniqueExistentialEquivalenceDistribution of (P -> lambda(z, in(pair(x, z), h)), Q -> lambda(z, in(pair(x, z), f))))
      val inFAndG = have(
        (functional(f), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (existsOne(y, in(pair(x, y), h)))
      ) by Tautology.from(lastStep, xInDomFOne)

      have(
        (functional(f), functional(g), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))))) |- in(x, domH) ==> existsOne(y, in(pair(x, y), h))
      ) by Tautology.from(inFAndG, notInF, notInG, domHDef)
      thenHave(
        (functional(f), functional(g), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))))) |- exists(y, in(pair(x, y), h)) ==> existsOne(
          y,
          in(pair(x, y), h)
        )
      ) by Substitution.apply2(false, domHIsDomain)
      thenHave(
        (functional(f), functional(g), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))))) |- forall(
          x,
          exists(y, in(pair(x, y), h)) ==> existsOne(y, in(pair(x, y), h))
        )
      ) by RightForall
    }

    have(thesis) by Tautology.from(functional.definition of f -> h, isRelation, isFunctional)
  }

  /**
   * Theorem --- Union of a Set of Functions is a Function
   *
   * Given a set `z` of functions (weakly or [[reflexive]]ly) totally ordered by the [[subset]] relation on the elements' domains ([[relationDomain]]), `∪ z` is [[functional]] (in particular, with domain as the union of the elements' domains).
   */
  // val unionOfFunctionSet = Lemma(
  //   forall(t, in(t, z) ==> functional(t)) /\ forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(relationDomain(x), relationDomain(y)) \/ subset(relationDomain(y), relationDomain(x))))) |- functional(union(z))
  // ) {
  //   ???
  // }
}
