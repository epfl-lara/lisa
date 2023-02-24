package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.mathematics.FirstOrderLogic.*
import lisa.utils.parsing.FOLPrinter.*

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
   * Theorem --- a set is an element of `x \cup y` iff it is an element of `x` or `y`
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
        andThen(applySubst(upairax, false))
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
   * Theorem --- A power set is never empty.
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
   * Theorem --- If a set belongs to a singleton, it must be the single element.
   */
  val singletonHasNoExtraElements = Theorem(
    in(y, singleton(x)) <=> (x === y)
  ) {
    // specialization of the pair axiom to a singleton

    have(in(y, unorderedPair(x, x)) <=> (x === y) \/ (x === y)) by InstFunSchema(Map(x -> x, y -> x, z -> y))(pairAxiom)
    thenHave(in(y, singleton(x)) <=> (x === y)) by Restate
  }

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
   * Theorem --- Two unordered pairs are equal iff their elements are equal pairwise.
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
   *  pair(a, b) === {{a}, {a, b}}
   *
   *  pair(a, b) === pair(c, d) iff a === c and b === d
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
   * There does not exist a set of all sets. Alternatively, its existence, with
   * the comprehension schema and Russel's paradox, produces a contradiction.
   */
  val noUniversalSet = Theorem(
    ∀(z, in(z, x)) |- ()
  ) {
    have(in(x, x) |- ()) by Restate.from(selfNonInclusion)
    thenHave(∀(z, in(z, x)) |- ()) by LeftForall
  }

  /**
   * Theorem --- The power set of any set is not a proper subset of it.
   */
  val powerSetNonInclusion = Theorem(
    Exists(x, properSubset(powerSet(x), x)) |- ()
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
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val setIntersection = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))(setIntersectionUniqueness)

  val unaryIntersectionUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by UniqueComprehension(union(x), lambda(Seq(t, z), ∀(b, in(b, x) ==> in(t, b))))
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
  val unaryIntersection = DEF(x) --> The(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))(unaryIntersectionUniqueness)

  val setDifferenceUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))) by UniqueComprehension(x, lambda(Seq(t, z), !in(t, y)))
  }

  /**
   * Binary Set Difference --- Given two sets, produces the set that contains
   * elements in the first but not in the second. `x - y = {z ∈ x | ! z ∈
   * y}` The proofs are guaranteed and generated by [[uniqueComprehension]].
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
   * The first element of an ordered [[pair]] --- `first p = \cup \cap p`
   *
   * If `p = (a, b) = {{a}, {a, b}}`, `\cap p = {a}`, and `\cup \cap p = a`.
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage.
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
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val cartesianProduct =
    DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))(cartesianProductUniqueness)

  /**
   * Theorem --- a pair is in the set `x * y` iff its elements are in `x` and
   * `y` respectively.
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
    // (a, b) \in x * y ==> a \in x /\ b \in y
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
  val relation = DEF(r) --> ∃(a, ∃(b, subset(r, cartesianProduct(a, b))))

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
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
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
   * The proofs are guaranteed and generated by [[uniqueComprehension]].
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
   * Functional --- A binary [[relation]] is functional if it maps every element in its domain
   * to a unique element (in its range).
   *
   *     `functional(f) ⇔ relation(f) /\ \∀ x. (\exists y. (x, y) \in f) \Rightarrow (\exists! y. (x, y) \in f)`
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
   * Set of functions --- All functions from `x` to `y`, denoted `x \to y` or
   * `\to(x, y)`.
   *
   * Since functions from `x` to `y` contain pairs of the form `(a, b) | a \in
   * x, b \in y`, it is a filtering on the power set of their product, i.e. `x
   * \to y \subseteq PP(x * y)`.
   */
  val setOfFunctions = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))(setOfFunctionsUniqueness)

  /**
   * Function From (x to y) --- denoted  `f \in x \to y` or `f: x \to y`.
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

      val quantification = have((prem, ∃!(z, ((z === y) <=> in(pair(x, y), f)))) |- ∃!(z, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅)))))) subproof {
        have((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅)))))) by RightForall
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
        thenHave(
          (prem, ∃(z, ∀(y, ((z === y) <=> in(pair(x, y), f))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
        ) by LeftExists
        thenHave((prem, ∃!(z, in(pair(x, z), f))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) by Restate
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
        have((!prem, ∃!(z, ((z === y) <=> (y === ∅)))) |- ∃!(z, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅)))))) subproof {
          have((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∀(y, (z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by RightForall
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
          thenHave(
            (!prem, ∃(z, ∀(y, ((z === y) <=> (y === ∅))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
          ) by LeftExists
          thenHave((!prem, ∃!(z, (z === ∅))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) by Restate
        }

      have(thesis) by Cut(emptyPrem, quantification)
    }

    val negRhs = thenHave(() |- (prem, ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅)))))) by Restate

    have(thesis) by Cut.withParameters(prem)(negRhs, positive)
  }

  /**
   * Function application --- denoted `f(x)`. The unique element `z` such that
   * `(x, z) \in f` if it exists and `f` is functional, [[emptySet]] otherwise.
   */
  val app =
    DEF(f, x) --> The(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))(functionApplicationUniqueness)

  /**
   * Surjective (function) --- a function `f: x \to y` is surjective iff it
   * maps to every `b \in y` from atleast one `a \in x`.
   *
   * `surjective(f, x, y) = f \in x \to y \land \∀ b \in y. (\exists a \in x. f(a) = b)`
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))

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
  val injective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> (∃(a, in(a, x) /\ in(pair(a, b), f)) ==> ∃!(a, in(a, x) /\ in(pair(a, b), f))))

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
   * `f^-1`, is a function from `y` to `x` such that `\∀ a \in x, b \in y.
   * f(f^-1(b)) = b /\ f^-1(f(b)) = b`.
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
      thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ subset(y, x)) by Substitution(subsetAxiom)
      thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ forall(t, in(t, y) ==> in(t, x))) by Substitution(subsetAxiom of (x -> y, y -> x))
      andThen(applySubst(universalConjunctionCommutation of (P -> lambda(t, in(t, x) ==> in(t, y)), Q -> lambda(t, in(t, y) ==> in(t, x)))))
      andThen(applySubst(extensionalityAxiom))
      thenHave(thesis) by Restate
  }

  val functionalOverImpliesDomain = Theorem(
    functionalOver(f, x) |- (relationDomain(f) === x)
  ) {
    have(thesis) by Tautology.from(functionalOver.definition)
  }

  val functionFromImpliesDomainEq = Theorem(
    functionFrom(f, x, y) |- (relationDomain(f) === x)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(thesis) by Tautology.from(functionFrom.definition, funSetDef, functionalOver.definition)
  }

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
    val existsZdom = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, relationDomain(f)) /\ (app(f, z) === y))) by Tautology.from(yInRange, surjective.definition of (y -> powerSet(x)), inRangeImpliesPullbackExists of (z -> y), functionFromImpliesFunctional of (y -> powerSet(x)))
    val xeqdom = thenHave((ydef, surjective(f, x, powerSet(x)), (relationDomain(f) === x)) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by RightSubstEq(List((x, relationDomain(f))), lambda(x, ∃(z, in(z, x) /\ (app(f, z) === y))))
    val existsZ = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by Tautology.from(surjective.definition of (y -> powerSet(x)), functionFromImpliesDomainEq of (y -> powerSet(x)), xeqdom)

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
  show
}
