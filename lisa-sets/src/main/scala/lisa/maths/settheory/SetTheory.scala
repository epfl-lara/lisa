package lisa.maths.settheory

import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import scala.collection.immutable.{Map => ScalaMap}

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
  private val f = variable
  private val g = variable

  private val P = predicate[1]
  private val Q = predicate[1]
  private val R = predicate[2]
  private val schemPred = predicate[1]

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
   * have(∃(z, ∀(t, in(t, z) ⇔ myProperty(t))) ⊢ ∃!(z, ∀(t, in(t, z) ⇔ myProperty(t)))) by InstSchema(ScalaMap(schemPred -> (t, myProperty(t))))`
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
    thenHave((fprop(z) /\ (z === a), (z === a)) |- fprop(a)) by RightSubstEq.withParametersSimple(List((z, a)), lambda(Seq(z), fprop(z)))
    val forward = thenHave(fprop(z) |- (z === a) ==> fprop(a)) by Restate

    // backward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    val instLhs = thenHave(fprop(z) |- prop(z)) by InstantiateForall(t)
    val instRhs = thenHave(fprop(a) |- prop(a)) by InstSchema(ScalaMap(z -> a))

    have((fprop(z), fprop(a)) |- prop(z) /\ prop(a)) by RightAnd(instLhs, instRhs)
    thenHave(fprop(z) /\ fprop(a) |- in(t, a) <=> in(t, z)) by Tautology
    val extLhs = thenHave(fprop(z) /\ fprop(a) |- ∀(t, in(t, a) <=> in(t, z))) by RightForall
    val extRhs = have(∀(t, in(t, a) <=> in(t, z)) <=> (a === z)) by InstSchema(ScalaMap(x -> a, y -> z))(extensionalityAxiom)

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
  val setUnion: ConstantFunctionLabel[2] = DEF(x, y) --> union(unorderedPair(x, y))

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
        val tax = thenHave((in(z, a), a === x) |- in(z, x)) by RightSubstEq.withParametersSimple(List((a, x)), lambda(a, in(z, a)))

        have((in(z, a), a === y) |- in(z, a)) by Hypothesis
        val tay = thenHave((in(z, a), a === y) |- in(z, y)) by RightSubstEq.withParametersSimple(List((a, y)), lambda(a, in(z, a)))

        have((in(z, a), (a === x) \/ (a === y)) |- (in(z, x), in(z, y))) by LeftOr(tax, tay)
        thenHave((in(z, a), in(a, unorderedPair(x, y))) |- (in(z, x), in(z, y))) by Substitution.ApplyRules(upairax)
        thenHave((in(z, a) /\ in(a, unorderedPair(x, y))) |- (in(z, x), in(z, y))) by Restate
        thenHave(∃(a, in(z, a) /\ in(a, unorderedPair(x, y))) |- (in(z, x), in(z, y))) by LeftExists
        thenHave(thesis) by Restate
      }

      val bwd = have(((in(z, x) \/ in(z, y)) ==> ∃(a, in(z, a) /\ in(a, unorderedPair(x, y))))) subproof {
        have((in(z, x), (a === x)) |- in(z, x)) by Hypothesis
        thenHave((in(z, x), (a === x)) |- in(z, a)) by RightSubstEq.withParametersSimple(List((a, x)), lambda(a, in(z, a)))
        thenHave((in(z, x), (a === x)) |- in(z, a) /\ ((a === x) \/ (a === y))) by Tautology
        andThen(Substitution.applySubst(upairax, false))
        thenHave((in(z, x), (a === x)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by RightExists
        thenHave((in(z, x), (x === x)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by InstSchema(ScalaMap(a -> x))
        val tax = thenHave((in(z, x)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate

        have((in(z, y), (a === y)) |- in(z, y)) by Hypothesis
        thenHave((in(z, y), (a === y)) |- in(z, a)) by RightSubstEq.withParametersSimple(List((a, y)), lambda(a, in(z, a)))
        thenHave((in(z, y), (a === y)) |- in(z, a) /\ ((a === x) \/ (a === y))) by Tautology
        andThen(Substitution.applySubst(upairax, false))
        thenHave((in(z, y), (a === y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by RightExists
        thenHave((in(z, y), (y === y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by InstSchema(ScalaMap(a -> y))
        val tay = thenHave((in(z, y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate

        have((in(z, x) \/ in(z, y)) |- ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by LeftOr(tax, tay)
        thenHave(thesis) by Restate
      }

      val existsSubst = have(∃(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> (in(z, x) \/ in(z, y))) by RightIff(fwd, bwd)

      have(in(z, union(unorderedPair(x, y))) <=> ∃(a, in(z, a) /\ in(a, unorderedPair(x, y)))) by Restate.from(ta)
      thenHave(thesis) by Substitution.ApplyRules(existsSubst, unionDef)
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
  val successor = DEF(x: Variable) --> union(unorderedPair(x, singleton(x)))

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

    have(∀(x, (x === successor(y)) <=> (x === union(unorderedPair(y, unorderedPair(y, y)))))) by InstSchema(ScalaMap(x -> y))(successor.definition)
    thenHave(((successor(y) === successor(y)) <=> (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))))) by InstantiateForall(successor(y))
    val succDef = thenHave((successor(y) === union(unorderedPair(y, unorderedPair(y, y))))) by Restate
    val inductDef = have(inductive(x) <=> in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x))) by Restate.from(inductive.definition)

    have((in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Restate
    val succEq = thenHave(
      (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(successor(y), x))
    ) by RightSubstEq.withParametersSimple(
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
    ) by RightSubstIff.withParametersSimple(
      List((∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)), ∀(y, in(y, x) ==> in(successor(y), x)))),
      lambda(form, in(∅, x) /\ form)
    )
    val substituted = thenHave(
      (
        inductive(x) <=> in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x)),
        ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, in(y, x) ==> in(successor(y), x)),
        in(∅, x) /\ ∀(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
      ) |- inductive(x)
    ) by RightSubstIff.withParametersSimple(List((inductive(x), in(∅, x) /\ ∀(y, in(y, x) ==> in(successor(y), x)))), lambda(form, form))
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
   *    `y ∈ x ⊢ ! x = ∅`
   */
  val setWithElementNonEmpty = Theorem(
    in(y, x) |- !(x === ∅)
  ) {
    have((x === ∅) |- !in(y, x)) by Substitution.ApplyRules(x === ∅)(emptySetAxiom of (x := y))
  }

  /**
   * Theorem --- A set containing no elements is equal to the empty set.
   *
   *    `∀ y. ! y ∈ x ⊢ x = ∅`
   *
   * Converse of the empty set axiom ([[emptySetAxiom]]).
   */
  val setWithNoElementsIsEmpty = Theorem(
    ∀(y, !in(y, x)) |- (x === ∅)
  ) {
    have(!in(y, ∅)) by InstSchema(ScalaMap(x -> y))(emptySetAxiom)
    thenHave(() |- (!in(y, ∅), in(y, x))) by Weakening
    val lhs = thenHave(in(y, ∅) ==> in(y, x)) by Restate

    have(!in(y, x) |- !in(y, x)) by Hypothesis
    thenHave(!in(y, x) |- (!in(y, x), in(y, ∅))) by Weakening
    val rhs = thenHave(!in(y, x) |- in(y, x) ==> in(y, ∅)) by Restate

    have(!in(y, x) |- in(y, x) <=> in(y, ∅)) by RightIff(lhs, rhs)
    thenHave(∀(y, !in(y, x)) |- in(y, x) <=> in(y, ∅)) by LeftForall
    val exLhs = thenHave(∀(y, !in(y, x)) |- ∀(y, in(y, x) <=> in(y, ∅))) by RightForall

    have(∀(z, in(z, x) <=> in(z, ∅)) <=> (x === ∅)) by InstSchema(ScalaMap(x -> x, y -> ∅))(extensionalityAxiom)
    val exRhs = thenHave(∀(y, in(y, x) <=> in(y, ∅)) <=> (x === ∅)) by Restate

    have(∀(y, !in(y, x)) |- (∀(y, in(y, x) <=> in(y, ∅)) <=> (x === ∅)) /\ ∀(y, in(y, x) <=> in(y, ∅))) by RightAnd(exLhs, exRhs)
    thenHave(∀(y, !in(y, x)) |- (x === ∅)) by Tautology
  }

  /**
   * Theorem --- The empty set is a subset of every set.
   *
   *    `∅ ⊆ x`
   */
  val emptySetIsASubset = Theorem(
    subset(∅, x)
  ) {
    have(in(y, ∅) ==> in(y, x)) by Weakening(emptySetAxiom of (x := y))
    val rhs = thenHave(∀(y, in(y, ∅) ==> in(y, x))) by RightForall
    have(thesis) by Tautology.from(subsetAxiom of (x := ∅, y := x), rhs)
  }

  /**
   * Theorem --- If a set is a subset of the empty set, it is empty.
   *
   *    `x ⊆ ∅ <=> a = ∅`
   */
  val emptySetIsItsOwnOnlySubset = Theorem(
    subset(x, emptySet) <=> (x === emptySet)
  ) {
    val fwd = have(subset(x, emptySet) |- (x === emptySet)) subproof {
      have(subset(x, emptySet) |- forall(z, in(z, x) ==> in(z, emptySet))) by Weakening(subsetAxiom of y -> emptySet)
      thenHave(subset(x, emptySet) |- in(z, x) ==> in(z, emptySet)) by InstantiateForall(z)
      have(subset(x, emptySet) |- !in(z, x)) by Tautology.from(lastStep, emptySetAxiom of x -> z)
      thenHave(subset(x, emptySet) |- forall(z, !in(z, x))) by RightForall

      have(thesis) by Cut(lastStep, setWithNoElementsIsEmpty)
    }

    val bwd = have((x === emptySet) |- subset(x, emptySet)) subproof {
      have(subset(emptySet, emptySet)) by Restate.from(emptySetIsASubset of x -> emptySet)
      thenHave(thesis) by Substitution.ApplyRules(x === emptySet)
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
    have(thesis) by Tautology.from(emptySetIsASubset, powerAxiom of (x := ∅, y := x), setWithElementNonEmpty of (y := ∅, x := powerSet(x)))
  }

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
    thenHave(subset(x, x) <=> ⊤) by Substitution.ApplyRules(closedFormulaUniversal)
    thenHave(thesis) by Restate
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

    have(in(y, unorderedPair(x, x)) <=> (x === y) \/ (x === y)) by InstSchema(ScalaMap(x -> x, y -> x, z -> y))(pairAxiom)
    thenHave(in(y, singleton(x)) <=> (x === y)) by Restate
  }

  /**
   * Theorem --- Every set is a member of its power set.
   *
   *    `x ∈ P(x)`
   */
  val elemInItsPowerSet = Theorem(
    in(x, powerSet(x))
  ) {
    have(thesis) by Tautology.from(powerAxiom of (y := x), subsetReflexivity)
  }

  /**
   * Lemma --- The power set of the empty set is the set containing the empty set.
   *
   *    `P(∅) = {∅}`
   */
  val powerSetEmptySet = Theorem(
    powerSet(∅) === singleton(∅)
  ) {
    val powerAx = have(in(x, powerSet(∅)) <=> subset(x, ∅)) by Weakening(powerAxiom of (y := ∅))

    have(in(x, powerSet(∅)) <=> in(x, singleton(∅))) by Tautology.from(
      powerAx,
      emptySetIsItsOwnOnlySubset,
      singletonHasNoExtraElements of (y := x, x := ∅)
    )
    val ext = thenHave(∀(x, in(x, powerSet(∅)) <=> in(x, singleton(∅)))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x := powerSet(∅), y := singleton(∅)))
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
    have(thesis) by Tautology.from(pairAxiom of (z := x))
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
    val lhs = have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstSchema(ScalaMap(x -> x, y -> y, z -> z))(pairAxiom)
    have((z === y) |- (z === y)) by Hypothesis
    val rhs = thenHave((z === y) |- (z === x) \/ (z === y)) by Restate
    val factset = have((z === y) |- (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    thenHave((z === y) |- in(z, unorderedPair(x, y))) by Tautology
    thenHave((y === y) |- in(y, unorderedPair(x, y))) by InstSchema(ScalaMap(z -> y))
    thenHave(in(y, unorderedPair(x, y))) by LeftRefl
  }

  /**
   * Theorem --- The [[unorderedPair]] is, in fact, unordered.
   *
   *    `{x, y} = {y, x}`
   */
  val unorderedPairSymmetry = Theorem(
    unorderedPair(x, y) === unorderedPair(y, x)
  ) {
    have(in(z, unorderedPair(y, x)) <=> in(z, unorderedPair(x, y))) by Substitution.ApplyRules(pairAxiom)(pairAxiom of (x := y, y := x))
    thenHave(∀(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))) by RightForall
    thenHave(thesis) by Substitution.ApplyRules(extensionalityAxiom)
  }

  val unorderedPairDeconstruction = Theorem(
    (unorderedPair(a, b) === unorderedPair(c, d)) ⊢ (((a === c) ∧ (b === d)) ∨ ((a === d) ∧ (b === c)))
  ) {
    val s1 = have(Substitution.applySubst(unorderedPair(a, b) === unorderedPair(c, d))(pairAxiom of (x -> a, y -> b)))
    val base = have(Substitution.applySubst(s1)(pairAxiom of (x -> c, y -> d)))

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
      val step2 = thenHave((y === x, in(z, y)) |- in(z, x)) by Substitution.ApplyRules(y === x)
      have(in(z, y) /\ in(y, X) |- in(z, x)) by Tautology.from(pairAxiom of (y -> x, z -> y), step2)
      val step4 = thenHave(∃(y, in(z, y) /\ in(y, X)) |- in(z, x)) by LeftExists
      have(in(z, union(X)) ==> in(z, x)) by Tautology.from(unionAxiom of (x -> X), step4)
    }

    have(in(z, union(X)) <=> in(z, x)) by RightIff(forward, backward)
    thenHave(∀(z, in(z, union(X)) <=> in(z, x))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x -> union(X), y -> x)))
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
    thenHave((a === c, b === d) |- unorderedPair(a, b) === unorderedPair(c, d)) by RightSubstEq.withParametersSimple(
      List((a, c), (b, d)),
      lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(x, y))
    )
    val lhs = thenHave(Set((a === c) /\ (b === d)) |- unorderedPair(a, b) === unorderedPair(c, d)) by Restate

    have(unorderedPair(a, b) === unorderedPair(b, a)) by InstSchema(ScalaMap(x -> a, y -> b))(unorderedPairSymmetry)
    thenHave((a === d, b === c) |- (unorderedPair(a, b) === unorderedPair(c, d))) by RightSubstEq.withParametersSimple(
      List((a, d), (b, c)),
      lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(y, x))
    )
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
    val reflLhs = have(in(x, singleton(x)) <=> (x === x)) by InstSchema(ScalaMap(y -> x))(singletonHasNoExtraElements)

    val reflRhs = have((x === x)) by RightRefl
    have((x === x) /\ (in(x, singleton(x)) <=> (x === x))) by RightAnd(reflLhs, reflRhs)
    val lhs = thenHave(in(x, singleton(x))) by Tautology

    val rhs = have(in(x, singleton(x)) |- !(singleton(x) === ∅)) by InstSchema(ScalaMap(y -> x, x -> singleton(x)))(setWithElementNonEmpty)

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
    have(∀(z, in(z, singleton(x)) <=> in(z, singleton(y))) <=> (singleton(x) === singleton(y))) by InstSchema(ScalaMap(x -> singleton(x), y -> singleton(y)))(extensionalityAxiom)
    thenHave((singleton(x) === singleton(y)) |- ∀(z, in(z, singleton(x)) <=> in(z, singleton(y)))) by Tautology
    val singiff = thenHave((singleton(x) === singleton(y)) |- in(z, singleton(x)) <=> in(z, singleton(y))) by InstantiateForall(z)

    val singX = have(in(z, singleton(x)) <=> (z === x)) by InstSchema(ScalaMap(y -> z))(singletonHasNoExtraElements)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(x)) <=> in(z, singleton(y))) /\ (in(z, singleton(x)) <=> (z === x))) by RightAnd(singiff, singX)
    val yToX = thenHave((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x))) by Tautology

    val singY = have(in(z, singleton(y)) <=> (z === y)) by InstSchema(ScalaMap(x -> y))(singX)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x)) /\ (in(z, singleton(y)) <=> (z === y))) by RightAnd(yToX, singY)
    thenHave((singleton(x) === singleton(y)) |- ((z === x) <=> (z === y))) by Tautology
    thenHave((singleton(x) === singleton(y)) |- ((x === x) <=> (x === y))) by InstSchema(ScalaMap(z -> x))

    thenHave((singleton(x) === singleton(y)) |- (x === y)) by Restate
    val fwd = thenHave((singleton(x) === singleton(y)) ==> (x === y)) by Tautology

    // backward direction
    //  x === y |- {x} === {y}
    have(singleton(x) === singleton(x)) by RightRefl
    thenHave((x === y) |- singleton(x) === singleton(y)) by RightSubstEq.withParametersSimple(List((x, y)), lambda(a, singleton(x) === singleton(a)))
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
        val za = thenHave((in(a, x) /\ in(b, x), (z === a)) |- in(z, x)) by RightSubstEq.withParametersSimple(List((z, a)), lambda(a, in(a, x)))
        have(in(a, x) /\ in(b, x) |- in(b, x)) by Restate
        val zb = thenHave((in(a, x) /\ in(b, x), (z === b)) |- in(z, x)) by RightSubstEq.withParametersSimple(List((z, b)), lambda(a, in(a, x)))

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
      thenHave(Set((a === c), (b === d)) |- (pair(a, b) === pair(c, d))) by RightSubstEq.withParametersSimple(List((a, c), (b, d)), lambda(Seq(x, y), pair(a, b) === pair(x, y)))
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
      ) by RightSubstIff.withParametersSimple(
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
      andThen(Substitution.applySubst(unorderedPairExtensionality of (a -> a, b -> b, c -> c, d -> d))) // {a, b} = {c, d}
      andThen(Substitution.applySubst(unorderedPairExtensionality of (a -> a, b -> a, c -> c, d -> d))) //    {a} = {c, d}
      andThen(Substitution.applySubst(unorderedPairExtensionality of (a -> a, b -> b, c -> c, d -> c))) // {a, b} = {c}
      andThen(Substitution.applySubst(unorderedPairExtensionality of (a -> a, b -> a, c -> c, d -> c))) //    {a} = {c}
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

    have(!(X === ∅) ==> ∃(y, in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)))) by InstSchema(ScalaMap(x -> X))(foundationAxiom)
    val lhs = thenHave(!(X === ∅) |- ∃(y, in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)))) by Restate

    have(in(y, X) |- in(y, X) <=> (x === y)) by Weakening(singletonHasNoExtraElements)
    val innerRhs = thenHave(in(y, X) |- (x === y)) by Tautology

    have((in(x, X), (in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by Hypothesis
    thenHave((in(x, X), ∀(z, in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by LeftForall
    thenHave((in(x, X), ∀(z, in(z, X) ==> !in(z, x)), in(x, X)) |- in(x, X) ==> !in(x, x)) by InstSchema(ScalaMap(z -> x, y -> x))
    val coreRhs = thenHave(in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x)) |- !in(x, x)) by Restate

    // now we need to show that the assumption is indeed true
    // this requires destruction of the existential quantifier in lhs
    have(in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x)) |- in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x))) by Hypothesis
    val innerRhs2 = thenHave((in(y, X) /\ ∀(z, in(z, X) ==> !in(z, y)), x === y) |- in(x, X) /\ ∀(z, in(z, X) ==> !in(z, x))) by LeftSubstEq.withParametersSimple(
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

    val rhs = have(in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x)) by InstSchema(ScalaMap(x -> powerSet(x), y -> x))(powerAxiom)

    have(subset(powerSet(x), x) |- subset(powerSet(x), x) /\ (in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x))) by RightAnd(lhs, rhs)
    val contraLhs = thenHave(subset(powerSet(x), x) |- in(powerSet(x), powerSet(x))) by Tautology

    val contraRhs = have(!in(powerSet(x), powerSet(x))) by InstSchema(ScalaMap(x -> powerSet(x)))(selfNonInclusion)

    have(subset(powerSet(x), x) |- !in(powerSet(x), powerSet(x)) /\ in(powerSet(x), powerSet(x))) by RightAnd(contraLhs, contraRhs)
    thenHave(subset(powerSet(x), x) |- ()) by Restate
    thenHave(subset(powerSet(x), x) |- (x === powerSet(x))) by Weakening
    thenHave(properSubset(powerSet(x), x) |- ()) by Restate
    thenHave(∃(x, properSubset(powerSet(x), x)) |- ()) by LeftExists
  }

  val inclusionAntiSymmetric = Theorem(
    !(in(x, y) /\ in(y, x))
  ) {
    assume(in(x, y))
    assume(in(y, x))

    // consider the set u = {x, y}
    val u = unorderedPair(x, y)

    // u is not the empty set
    have(in(x, u)) by Weakening(firstElemInPair)
    have(!(u === emptySet)) by Tautology.from(lastStep, setWithElementNonEmpty of (y -> x, x -> u))

    // by Foundation, there must be an inclusion minimal element in u
    val minimal = have(exists(z, in(z, u) /\ forall(t, in(t, u) ==> !in(t, z)))) by Tautology.from(lastStep, foundationAxiom of x -> u)
    // negation = forall(z, in(z, u) ==> exists(t, in(t, u) /\ in(t, z)))

    // it can only be x or y
    val zxy = have(in(z, u) <=> ((z === x) \/ (z === y))) by Weakening(pairAxiom)

    // but x \cap u contains y, and y \cap u contains x
    have(in(x, u) /\ in(x, y)) by Tautology.from(firstElemInPair)
    thenHave((z === y) |- in(x, u) /\ in(x, z)) by Substitution.ApplyRules(z === y)
    val zy = thenHave((z === y) |- exists(t, in(t, u) /\ in(t, z))) by RightExists

    have(in(y, u) /\ in(y, x)) by Tautology.from(secondElemInPair)
    thenHave((z === x) |- in(y, u) /\ in(y, z)) by Substitution.ApplyRules(z === x)
    val zx = thenHave((z === x) |- exists(t, in(t, u) /\ in(t, z))) by RightExists

    // this is a contradiction
    have(in(z, u) ==> exists(t, in(t, u) /\ in(t, z))) by Tautology.from(zxy, zx, zy)
    thenHave(forall(z, in(z, u) ==> exists(t, in(t, u) /\ in(t, z)))) by RightForall

    have(thesis) by Tautology.from(lastStep, minimal)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Operations on Sets
   */

  val setIntersectionUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))) by UniqueComprehension(x, lambda(t, in(t, y)))
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

  val setIntersectionCommutativity = Theorem(
    setIntersection(x, y) === setIntersection(y, x)
  ) {
    sorry
  }

  val setIntersectionMembership = Theorem(
    in(t, setIntersection(x, y)) <=> (in(t, x) /\ in(t, y))
  ) {
    sorry
  }

  extension (x: Term) {
    infix def ∩(y: Term) = setIntersection(x, y)
  }

  val intersectionOfSubsets = Lemma(
    subset(x, y) |- setIntersection(x, y) === x
  ) {
    have(forall(t, in(t, setIntersection(x, y)) <=> (in(t, x) /\ in(t, y)))) by InstantiateForall(setIntersection(x, y))(setIntersection.definition)
    val txy = thenHave(in(t, setIntersection(x, y)) <=> (in(t, x) /\ in(t, y))) by InstantiateForall(t)

    have(subset(x, y) |- forall(t, in(t, x) ==> in(t, y))) by Weakening(subsetAxiom)
    thenHave(subset(x, y) |- in(t, x) ==> in(t, y)) by InstantiateForall(t)

    have(subset(x, y) |- in(t, setIntersection(x, y)) <=> in(t, x)) by Tautology.from(lastStep, txy)
    thenHave(subset(x, y) |- forall(t, in(t, setIntersection(x, y)) <=> in(t, x))) by RightForall
    have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> setIntersection(x, y), y -> x))
  }

  val unaryIntersectionUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))))
  ) {
    val uniq = have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by UniqueComprehension(union(x), lambda(t, ∀(b, in(b, x) ==> in(t, b))))

    val lhs = have((in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))) |- ∀(b, in(b, x) ==> in(t, b)) /\ exists(b, in(b, x))) subproof {
      val unionAx = have(in(t, union(x)) |- exists(b, in(b, x) /\ in(t, b))) by Weakening(unionAxiom of (z -> t))

      have(in(b, x) /\ in(t, b) |- in(b, x)) by Restate
      thenHave(in(b, x) /\ in(t, b) |- exists(b, in(b, x))) by RightExists
      val exRed = thenHave(exists(b, in(b, x) /\ in(t, b)) |- exists(b, in(b, x))) by LeftExists

      have(in(t, union(x)) |- exists(b, in(b, x))) by Cut(unionAx, exRed)
      thenHave(thesis) by Tautology
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
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))) by UniqueComprehension(x, lambda(t, !in(t, y)))
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
    have(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ φ(t))))) by InstSchema(ScalaMap(z -> x))(comprehensionSchema)

    val conjunction = thenHave(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) by InstSchema(ScalaMap(φ -> lambda(t, ∀(y, P(y) ==> in(t, y)))))

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
    ) by RightSubstIff.withParametersSimple(List((∀(y, P(y) ==> in(t, y)), (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))

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
    have(thesis) by UniqueComprehension(union(p), lambda(t, ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p))))))
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
  val unionOfOrderedPair = Theorem(
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
        val zxy = have((b === unorderedPair(x, y)) |- in(z, b) <=> ((z === x) \/ (z === y))) by Substitution.ApplyRules(b === unorderedPair(x, y))(pairAxiom)
        val zxx = have((b === unorderedPair(x, x)) |- in(z, b) <=> ((z === x) \/ (z === x))) by Substitution.ApplyRules(b === unorderedPair(x, x))(pairAxiom of y -> x)

        have(in(b, pair(x, y)) /\ in(z, b) |- ((z === x) \/ (z === y))) by Tautology.from(bxy, zxy, zxx)
        thenHave(thesis) by LeftExists
      }

      val bwd = have(((z === x) \/ (z === y)) |- exists(b, in(b, pair(x, y)) /\ in(z, b))) subproof {
        val xyp = have(in(unorderedPair(x, y), pair(x, y))) by Restate.from(firstElemInPair of (x -> unorderedPair(x, y), y -> unorderedPair(x, x)))
        val zx = have((z === x) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(z === x)(firstElemInPair)
        val zy = have((z === y) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(z === y)(secondElemInPair)

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
  val pairUnaryIntersection = Theorem(
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
        val bp = thenHave(in(b, pair(x, y)) |- (b === singleton(x)) \/ (b === unorderedPair(x, y))) by Substitution.ApplyRules(pairAxiom of (z -> b, x -> unorderedPair(x, y), y -> singleton(x)))

        have(in(x, singleton(x))) by Restate.from(singletonHasNoExtraElements of (y -> x))
        val bxx = thenHave((b === singleton(x)) |- in(x, b)) by Substitution.ApplyRules((b === singleton(x)))

        have(in(x, unorderedPair(x, y))) by Restate.from(firstElemInPair)
        val bxy = thenHave((b === unorderedPair(x, y)) |- in(x, b)) by Substitution.ApplyRules((b === unorderedPair(x, y)))

        have(in(b, pair(x, y)) ==> in(x, b)) by Tautology.from(bp, bxx, bxy)
        val frClause = thenHave(forall(b, in(b, pair(x, y)) ==> in(x, b))) by RightForall

        have(thesis) by Tautology.from(defexp of (z -> x), exClause, frClause)
      }
      thenHave(thesis) by Substitution.ApplyRules((z === x))
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
  val pairUnionIntersectionEqual = Theorem(
    () |- (union(pair(x, y)) === unaryIntersection(pair(x, y))) <=> (x === y)
  ) {
    have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by Restate.from(pairAxiom)
    val unionPair = thenHave(in(z, union(pair(x, y))) <=> ((z === x) \/ (z === y))) by Substitution.ApplyRules(unionOfOrderedPair)

    val fwd = have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (x === y)) subproof {
      have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- forall(z, in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y))))) by Weakening(
        extensionalityAxiom of (x -> union(pair(x, y)), y -> unaryIntersection(pair(x, y)))
      )
      thenHave((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y)))) by InstantiateForall(z)

      have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (((z === x) \/ (z === y)) <=> (z === x))) by Tautology.from(lastStep, unionPair, pairUnaryIntersection)
      thenHave((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (((y === x) \/ (y === y)) <=> (y === x))) by InstSchema(ScalaMap(z -> y))
      thenHave(thesis) by Restate
    }

    val bwd = have((x === y) |- (union(pair(x, y)) === unaryIntersection(pair(x, y)))) subproof {
      have((x === y) |- in(z, union(pair(x, y))) <=> ((z === x) \/ (z === x))) by Substitution.ApplyRules(x === y)(unionPair)
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
  val firstInPairReduction = Theorem(
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
        thenHave((in(z, t), (t === x)) |- in(z, x)) by Substitution.ApplyRules(t === x)
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
    have(thesis) by Substitution.ApplyRules(lastStep)(unioneq)
  }

  /**
   * Theorem --- The [[secondInPairSingletone]] operation when applied to an
   * ordered pair produces the singleton containing the second element of the pair.
   *
   *    `secondSingleton((x, y)) = {y}`
   *
   * Used for [[secondInPair]] reduction.
   */
  val secondInPairSingletonReduction = Theorem(
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
      ) by Substitution.ApplyRules(zUnion, zInter, unEqInt)

      have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x)))) <=> (z === y)) subproof {
        val hypo = have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x)))) |- (((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))))) by Hypothesis
        thenHave((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), (x === y)) |- (((z === y) \/ (z === y)) /\ ((!(y === y)) ==> (!(z === x))))) by Substitution.ApplyRules(x === y)
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
  val secondInPairReduction = Theorem(
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
        thenHave((in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b), (b === y)) |- in(z, y)) by Substitution.ApplyRules(b === y)
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
   * Theorem --- Pair Reconstruction
   *
   * If `x` is a pair (i.e. `= (c, d)` for some `c` and `d`), then pair element
   * projection on it is invertible, so `x = (fst x, snd x)`.
   */
  val pairReconstruction = Lemma(
    exists(c, exists(d, pair(c, d) === x)) |- x === pair(firstInPair(x), secondInPair(x))
  ) {
    sorry
  }

  /**
   * Cartesian Products and Relations
   */

  val cartesianProductUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))) by UniqueComprehension(
      powerSet(powerSet(setUnion(x, y))),
      lambda(t, ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))
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
    () |- (cartesianProduct(x, emptySet) === emptySet) /\ (cartesianProduct(emptySet, x) === emptySet)
  ) {
    val xFirst = have(() |- (cartesianProduct(x, emptySet) === emptySet)) subproof {
      have(
        forall(t, in(t, cartesianProduct(x, emptySet)) <=> (in(t, powerSet(powerSet(setUnion(x, emptySet)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet)))))
      ) by InstantiateForall(cartesianProduct(x, emptySet))(cartesianProduct.definition of (y -> emptySet))
      val impl = thenHave(
        in(t, cartesianProduct(x, emptySet)) <=> (in(t, powerSet(powerSet(setUnion(x, emptySet)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet))))
      ) by InstantiateForall(t)

      val elemEmpty = have(in(t, emptySet) <=> (in(t, powerSet(powerSet(setUnion(x, emptySet)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet))))) subproof {
        val lhs = have(in(t, emptySet) |- (in(t, powerSet(powerSet(setUnion(x, emptySet)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet))))) by Weakening(
          emptySet.definition of (x -> t)
        )

        have((t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet) |- in(t, emptySet)) by Weakening(emptySet.definition of (x -> b))
        thenHave(exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet)) |- in(t, emptySet)) by LeftExists
        thenHave(exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet))) |- in(t, emptySet)) by LeftExists
        val rhs = thenHave(in(t, powerSet(powerSet(setUnion(x, emptySet)))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, emptySet))) |- in(t, emptySet)) by Weakening

        have(thesis) by Tautology.from(lhs, rhs)
      }

      have(in(t, cartesianProduct(x, emptySet)) <=> in(t, emptySet)) by Tautology.from(impl, elemEmpty)
      val ext = thenHave(forall(t, in(t, cartesianProduct(x, emptySet)) <=> in(t, emptySet))) by RightForall

      have(thesis) by Tautology.from(ext, extensionalityAxiom of (x -> cartesianProduct(x, emptySet), y -> emptySet))
    }

    val xSecond = have(() |- (cartesianProduct(emptySet, x) === emptySet)) subproof {
      have(
        forall(t, in(t, cartesianProduct(emptySet, y)) <=> (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y)))))
      ) by InstantiateForall(cartesianProduct(emptySet, y))(cartesianProduct.definition of (x -> emptySet))
      val impl = thenHave(
        in(t, cartesianProduct(emptySet, y)) <=> (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))))
      ) by InstantiateForall(t)

      val elemEmpty = have(in(t, emptySet) <=> (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))))) subproof {
        val lhs = have(in(t, emptySet) |- (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))))) by Weakening(
          emptySet.definition of (x -> t)
        )

        have((t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y) |- in(t, emptySet)) by Weakening(emptySet.definition of (x -> a))
        thenHave(exists(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y)) |- in(t, emptySet)) by LeftExists
        thenHave(exists(a, exists(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))) |- in(t, emptySet)) by LeftExists
        val rhs = thenHave(in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))) |- in(t, emptySet)) by Weakening

        have(thesis) by Tautology.from(lhs, rhs)
      }

      have(in(t, cartesianProduct(emptySet, y)) <=> in(t, emptySet)) by Tautology.from(impl, elemEmpty)
      val ext = thenHave(forall(t, in(t, cartesianProduct(emptySet, y)) <=> in(t, emptySet))) by RightForall

      have(thesis) by Tautology.from(ext of (y -> x), extensionalityAxiom of (x -> cartesianProduct(emptySet, x), y -> emptySet))
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
      thenHave((a === c, b === d, in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by RightSubstEq.withParametersSimple(List((a, c), (b, d)), lambda(Seq(a, b), in(a, x) /\ in(b, y)))
      thenHave(Set((a === c) /\ (b === d), in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by Restate
      andThen(Substitution.applySubst(pairExtensionality))
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
          val zab =
            thenHave((prem, (z === unorderedPair(a, b))) |- in(z, powerSet(setUnion(x, y)))) by RightSubstEq.withParametersSimple(
              List((z, unorderedPair(a, b))),
              lambda(a, in(a, powerSet(setUnion(x, y))))
            )
          have(prem |- in(unorderedPair(a, a), powerSet(setUnion(x, y)))) by Weakening(unorderedPairInPowerSet of (x -> setUnion(x, y), b -> a))
          val zaa =
            thenHave((prem, (z === unorderedPair(a, a))) |- in(z, powerSet(setUnion(x, y)))) by RightSubstEq.withParametersSimple(
              List((z, unorderedPair(a, a))),
              lambda(a, in(a, powerSet(setUnion(x, y))))
            )

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
  val elemOfPowerPowerUnion = Theorem(
    ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))
  ) {
    val upCD = have((in(c, x), in(d, y)) |- in(unorderedPair(c, d), powerSet(setUnion(x, y)))) subproof {

      have((in(c, x), in(d, y)) |- subset(unorderedPair(c, d), setUnion(x, y))) subproof {
        val zcd = have(in(z, unorderedPair(c, d)) <=> ((z === c) \/ (z === d))) by Restate.from(pairAxiom of (x -> c, y -> d))
        val zunion = have(in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))) by Restate.from(setUnionMembership)

        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.ApplyRules(z === c)(zunion)
        val zd = have((z === d) |- in(z, setUnion(x, y)) <=> (in(d, x) \/ in(d, y))) by Substitution.ApplyRules(z === d)(zunion)

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

        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.ApplyRules(z === c)(zunion)

        have(in(c, x) |- in(z, unorderedPair(c, c)) ==> in(z, setUnion(x, y))) by Tautology.from(zcd, zc)
        thenHave(in(c, x) |- forall(z, in(z, unorderedPair(c, c)) ==> in(z, setUnion(x, y)))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> unorderedPair(c, c), y -> setUnion(x, y)))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y -> setUnion(x, y), x -> unorderedPair(c, c)))

    }

    have((in(c, x), in(d, y)) |- in(pair(c, d), powerSet(powerSet(setUnion(x, y))))) subproof {

      have((in(c, x), in(d, y)) |- subset(pair(c, d), powerSet(setUnion(x, y)))) subproof {
        val zp = have(in(z, pair(c, d)) <=> ((z === unorderedPair(c, d)) \/ (z === unorderedPair(c, c)))) by Restate.from(pairAxiom of (x -> unorderedPair(c, d), y -> unorderedPair(c, c)))

        val zcc = have((z === unorderedPair(c, c), in(c, x)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.ApplyRules(z === unorderedPair(c, c))(upCC)
        val zcd = have((z === unorderedPair(c, d), in(c, x), in(d, y)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.ApplyRules(z === unorderedPair(c, d))(upCD)

        have((in(c, x), in(d, y)) |- in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y)))) by Tautology.from(zp, zcc, zcd)
        thenHave((in(c, x), in(d, y)) |- forall(z, in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y))))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> pair(c, d), y -> powerSet(setUnion(x, y))))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y -> powerSet(setUnion(x, y)), x -> pair(c, d)))

    }

    thenHave((t === pair(c, d), in(c, x), in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Substitution.ApplyRules(t === pair(c, d))
    thenHave(((t === pair(c, d)) /\ in(c, x) /\ in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Restate
    thenHave(exists(d, ((t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))) by LeftExists
    thenHave(thesis) by LeftExists
  }

  /**
   * Theorem --- the binary set union operation is commutative.
   *
   *    `a ∪ b = b ∪ a`
   */
  val unionCommutativity = Theorem(
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
  val unionSubsetFirst = Theorem(
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
  val unionSubsetSecond = Theorem(
    subset(b, setUnion(a, b))
  ) {
    have(thesis) by Substitution.ApplyRules(unionCommutativity)(unionSubsetFirst of (a -> b, b -> a))
  }

  /**
   * Theorem --- the union of two subsets of a set is still a subset of it.
   *
   *    `a ⊆ c ∧ b ⊆ c ⊢ a ∪ b ⊆ c`
   */
  val unionOfTwoSubsets = Theorem(
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
  val unionOfSubsetsOfDifferentSets = Theorem(
    subset(a, c) /\ subset(b, d) |- subset(setUnion(a, b), setUnion(c, d))
  ) {
    val unionDefab = have(in(z, setUnion(a, b)) <=> (in(z, a) \/ in(z, b))) by Restate.from(setUnionMembership of (x -> a, y -> b))
    val unionDefcd = unionDefab of (a -> c, b -> d)

    have(subset(a, c) |- forall(z, in(z, a) ==> in(z, c))) by Weakening(subsetAxiom of (x -> a, y -> c))
    val ac = thenHave(subset(a, c) |- in(z, a) ==> in(z, c)) by InstantiateForall(z)
    val bc = ac of (a -> b, c -> d)

    have(subset(a, c) /\ subset(b, d) |- in(z, setUnion(a, b)) ==> (in(z, c) \/ in(z, d))) by Tautology.from(unionDefab, ac, bc)
    thenHave(subset(a, c) /\ subset(b, d) |- in(z, setUnion(a, b)) ==> in(z, setUnion(c, d))) by Substitution.ApplyRules(unionDefcd)
    thenHave(subset(a, c) /\ subset(b, d) |- forall(z, in(z, setUnion(a, b)) ==> in(z, setUnion(c, d)))) by RightForall

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> setUnion(a, b), y -> setUnion(c, d)))
  }

  /**
   * Theorem --- the subset predicate is transitive.
   *
   *    `a ⊆ b ∧ b ⊆ c ⊢ a ⊆ c`
   */
  val subsetTransitivity = Theorem(
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
  val unionOfCartesianProducts = Theorem(
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

    val zcd =
      have(in(z, cxd) |- in(z, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Substitution.ApplyRules(unionCommutativity)(
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
      andThen(Substitution.applySubst(unionAxiom of (z -> unorderedPair(a, b), x -> r)))
    }
    val unionA = have(in(unorderedPair(a, b), union(r)) |- in(a, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(a, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, firstElemInPair of (x -> a, y -> b))
      thenHave(in(unorderedPair(a, b), union(r)) |- ∃(y, in(a, y) /\ in(y, union(r)))) by RightExists
      andThen(Substitution.applySubst(unionAxiom of (z -> a, x -> union(r))))
    }
    val unionB = have(in(unorderedPair(a, b), union(r)) |- in(b, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(b, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, secondElemInPair of (x -> a, y -> b))
      thenHave(in(unorderedPair(a, b), union(r)) |- ∃(y, in(b, y) /\ in(y, union(r)))) by RightExists
      andThen(Substitution.applySubst(unionAxiom of (z -> b, x -> union(r))))
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
      lambda(t, ∃(a, in(pair(t, a), r)))
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
      ) by RightSubstIff.withParametersSimple(List((∃(a, in(pair(t, a), r)), in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))), lambda(h, in(t, z) <=> h))
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
      lambda(t, ∃(a, in(pair(a, t), r)))
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
      ) by RightSubstIff.withParametersSimple(List((∃(a, in(pair(a, t), r)), in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))), lambda(h, in(t, z) <=> h))
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
   * Theorem --- the relation domain of the empty set is the empty set.
   */
  val domainOfEmptySetIsEmpty = Theorem(
    relationDomain(∅) === ∅
  ) {
    have(∀(t, in(t, relationDomain(∅)) <=> ∃(a, in(pair(t, a), ∅)))) by InstantiateForall(relationDomain(∅))(
      relationDomain.definition of (r := ∅)
    )
    val domainDef = thenHave(in(t, relationDomain(∅)) <=> ∃(a, in(pair(t, a), ∅))) by InstantiateForall(t) // todo: check if can be simplified with shortDefinition
    val contraPosDomainDef = have(!in(t, relationDomain(∅)) <=> ∀(a, !in(pair(t, a), ∅))) by Tautology.from(domainDef)
    have(!in(pair(t, a), ∅)) by Tautology.from(emptySetAxiom of (x := pair(t, a)))
    val nothingInEmpty = thenHave(∀(a, !in(pair(t, a), ∅))) by RightForall

    have(!in(t, relationDomain(∅))) by Tautology.from(nothingInEmpty, contraPosDomainDef)
    thenHave(∀(t, !in(t, relationDomain(∅)))) by RightForall

    have(thesis) by Tautology.from(lastStep, setWithNoElementsIsEmpty of (x := relationDomain(∅)))
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
   * Theorem --- If `r` is a relation, then `r` is a relation between its domain and its range.
   */
  val relationImpliesRelationBetweenDomainAndRange = Theorem(
    relation(r) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    // Lay out the definitions to apply them later
    have(∀(t, in(t, relationDomain(r)) <=> ∃(b, in(pair(t, b), r)))) by Definition(relationDomain, relationDomainUniqueness)(r)
    val relationDomainDef = thenHave(in(t, relationDomain(r)) <=> ∃(b, in(pair(t, b), r))) by InstantiateForall(t)

    have(∀(t, in(t, relationRange(r)) <=> ∃(a, in(pair(a, t), r)))) by Definition(relationRange, relationRangeUniqueness)(r)
    val relationRangeDef = thenHave(in(t, relationRange(r)) <=> ∃(a, in(pair(a, t), r))) by InstantiateForall(t)

    // Start the proof
    have(relation(r) |- ∃(x, ∃(y, relationBetween(r, x, y)))) by Tautology.from(relation.definition)

    have(relationBetween(r, x, y) |- subset(r, cartesianProduct(x, y))) by Tautology.from(relationBetween.definition of (a -> x, b -> y))
    have(relationBetween(r, x, y) |- ∀(t, in(t, r) ==> in(t, cartesianProduct(x, y)))) by Tautology.from(
      lastStep,
      subset.definition of (x -> r, y -> cartesianProduct(x, y))
    )
    thenHave(relationBetween(r, x, y) |- in(t, r) ==> in(t, cartesianProduct(x, y))) by InstantiateForall(t)
    thenHave((relationBetween(r, x, y), in(t, r)) |- in(t, cartesianProduct(x, y))) by Restate

    // Apply the definition of the cartesian product
    val relationDef = have((relationBetween(r, x, y), in(t, r)) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))) by Tautology.from(
      lastStep,
      elemOfCartesianProduct
    )

    // Show that x ⊇ relationDomain(r) and y ⊇ relationRange(r)
    val memberships = have((in(t, r), (t === pair(a, b))) |- in(a, relationDomain(r)) /\ in(b, relationRange(r))) subproof {
      have(in(t, r) |- in(t, r)) by Hypothesis
      val membership = thenHave((in(t, r), (t === pair(a, b))) |- in(pair(a, b), r)) by Substitution.ApplyRules(t === pair(a, b))

      assume(in(t, r))
      assume(t === pair(a, b))
      have(∃(b, in(pair(a, b), r))) by RightExists(membership)
      val left = have(in(a, relationDomain(r))) by Tautology.from(lastStep, relationDomainDef of (t -> a))

      have(∃(a, in(pair(a, b), r))) by RightExists(membership)
      val right = have(in(b, relationRange(r))) by Tautology.from(lastStep, relationRangeDef of (t -> b))

      have(thesis) by RightAnd(left, right)
    }

    // We can now reconstruct the definition of relationBetween(r, relationDomain(r), relationRange(r))
    have((t === pair(a, b)) |- (t === pair(a, b))) by Hypothesis
    val toCut = have((in(t, r), (t === pair(a, b))) |- (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))) by RightAnd(lastStep, memberships)

    have((t === pair(a, b)) /\ in(a, x) /\ in(b, y) |- (t === pair(a, b))) by Tautology
    have((in(t, r), (t === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))) by Cut(lastStep, toCut)

    // Re-add the existential quantifiers
    thenHave((in(t, r), (t === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r)))) by RightExists
    thenHave((in(t, r), (t === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by RightExists
    thenHave((in(t, r), ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by LeftExists
    thenHave((in(t, r), ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by LeftExists

    // Cut and rewrap the definition
    have((in(t, r), relationBetween(r, x, y)) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by Cut(
      relationDef,
      lastStep
    )
    have((in(t, r), relationBetween(r, x, y)) |- in(t, cartesianProduct(relationDomain(r), relationRange(r)))) by Tautology.from(
      lastStep,
      elemOfCartesianProduct of (x -> relationDomain(r), y -> relationRange(r))
    )
    thenHave(relationBetween(r, x, y) |- in(t, r) ==> in(t, cartesianProduct(relationDomain(r), relationRange(r)))) by Restate
    thenHave(relationBetween(r, x, y) |- ∀(t, in(t, r) ==> in(t, cartesianProduct(relationDomain(r), relationRange(r))))) by RightForall
    have(relationBetween(r, x, y) |- subset(r, cartesianProduct(relationDomain(r), relationRange(r)))) by Tautology.from(
      lastStep,
      subset.definition of (x -> r, y -> cartesianProduct(relationDomain(r), relationRange(r)))
    )
    have(relationBetween(r, x, y) |- relationBetween(r, relationDomain(r), relationRange(r))) by Tautology.from(
      lastStep,
      relationBetween.definition of (a -> relationDomain(r), b -> relationRange(r))
    )

    // Add the existential quantifier to finish the proofs
    thenHave(∃(y, relationBetween(r, x, y)) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists
    thenHave(∃(x, ∃(y, relationBetween(r, x, y))) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists

    have(thesis) by Tautology.from(lastStep, relation.definition)
  }

  /**
   * Theorem --- The Cartesian Product of two sets is a relation.
   */
  val cartesianProductIsRelation = Theorem(
    relation(cartesianProduct(x, y))
  ) {
    // trivially follows from the fact that a relation is a subset of the cartesian product
    have(relationBetween(cartesianProduct(x, y), x, y)) by Tautology.from(
      subsetReflexivity of (x := cartesianProduct(x, y)),
      relationBetween.definition of (r := cartesianProduct(x, y), a := x, b := y)
    )
    thenHave(∃(b, relationBetween(cartesianProduct(x, y), x, b))) by RightExists
    val relationSpec = thenHave(∃(a, ∃(b, relationBetween(cartesianProduct(x, y), a, b)))) by RightExists

    have(thesis) by Tautology.from(relationSpec, relation.definition of (r := cartesianProduct(x, y)))
  }

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

    thenHave((relation(f), relation(g)) |- relation(setUnion(f, g))) by Substitution.ApplyRules(relf, relg, relfug)
  }

  /**
   * Theorem --- Pair in Relation
   *
   * If a pair `(x, y)` exists in a relation `r` from `a` to `b`,
   * then `x` and `y` are elements of `a` and `b` respectively.
   */
  val pairInRelation = Lemma(
    relationBetween(r, a, b) /\ in(pair(x, y), r) |- in(x, a) /\ in(y, b)
  ) {
    assume(relationBetween(r, a, b))
    assume(in(pair(x, y), r))
    have(forall(t, in(t, r) ==> in(t, cartesianProduct(a, b)))) by Tautology.from(relationBetween.definition, subsetAxiom of (x -> r, y -> cartesianProduct(a, b)))
    thenHave(in(pair(x, y), r) ==> in(pair(x, y), cartesianProduct(a, b))) by InstantiateForall(pair(x, y))
    have(thesis) by Tautology.from(lastStep, pairInCartesianProduct of (x -> a, y -> b, a -> x, b -> y))
  }

  // TODO: any subset of a functional is functional
  // TODO: a functional over something restricted to x is still functional

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
  val emptySetRelation = Theorem(
    () |- relationBetween(emptySet, a, b)
  ) {
    have(thesis) by Tautology.from(emptySetIsASubset of (x -> cartesianProduct(a, b)), relationBetween.definition of (r -> emptySet))
  }

  /**
   * Theorem --- the empty relation is a relation on the empty set.
   */
  val emptySetRelationOnItself = Theorem(
    () |- relationBetween(emptySet, emptySet, emptySet)
  ) {
    have(thesis) by Restate.from(emptySetRelation of (a -> emptySet, b -> emptySet))
  }

  /**
   * Theorem --- empty relation on the empty set is reflexive.
   */
  val emptyRelationReflexiveOnItself = Theorem(
    () |- reflexive(emptySet, emptySet)
  ) {
    have(() |- in(y, emptySet) ==> in(pair(y, y), emptySet)) by Tautology.from(emptySetAxiom of (x -> y))
    val refCond = thenHave(() |- forall(y, in(y, emptySet) ==> in(pair(y, y), emptySet))) by RightForall

    have(thesis) by Tautology.from(reflexive.definition of (r -> emptySet, x -> emptySet), emptySetRelationOnItself, refCond)
  }

  /**
   * Theorem --- the empty relation is symmetric.
   */
  val emptyRelationSymmetric = Theorem(
    () |- symmetric(emptySet, a)
  ) {
    have(() |- in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet)) by Tautology.from(emptySetAxiom of (x -> pair(y, z)), emptySetAxiom of (x -> pair(z, y)))
    thenHave(() |- forall(z, in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet))) by RightForall
    val symCond = thenHave(() |- forall(y, forall(z, in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet)))) by RightForall

    have(thesis) by Tautology.from(symmetric.definition of (r -> emptySet, x -> a), emptySetRelation of (b -> a), symCond)
  }

  /**
   * Theorem --- the empty relation is irreflexive.
   */
  val emptyRelationIrreflexive = Theorem(
    () |- irreflexive(emptySet, a)
  ) {
    have(() |- in(y, a) ==> !in(pair(y, y), emptySet)) by Tautology.from(emptySetAxiom of (x -> pair(y, y)))
    val irrefCond = thenHave(() |- forall(y, in(y, a) ==> !in(pair(y, y), emptySet))) by RightForall

    have(thesis) by Tautology.from(irreflexive.definition of (r -> emptySet, x -> a), emptySetRelation of (b -> a), irrefCond)
  }

  /**
   * Theorem --- the empty relation is transitive.
   */
  val emptyRelationTransitive = Theorem(
    () |- transitive(emptySet, a)
  ) {
    have(() |- (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet)) by Tautology.from(emptySetAxiom of (x -> pair(w, y)))
    thenHave(() |- forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet))) by RightForall
    thenHave(() |- forall(y, forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet)))) by RightForall
    val trsCond = thenHave(() |- forall(w, forall(y, forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet))))) by RightForall

    have(thesis) by Tautology.from(transitive.definition of (r -> emptySet, x -> a), emptySetRelation of (b -> a), trsCond)
  }

  /**
   * Theorem --- the empty relation is an equivalence relation on the empty set.
   */
  val emptyRelationEquivalence = Theorem(
    () |- equivalence(emptySet, emptySet)
  ) {
    have(thesis) by Tautology.from(
      equivalence.definition of (r -> emptySet, x -> emptySet),
      emptyRelationReflexiveOnItself,
      emptyRelationSymmetric of (a -> emptySet),
      emptyRelationTransitive of (a -> emptySet)
    )
  }

  /**
   * Theorem --- the empty relation is anti-symmetric.
   */
  val emptyRelationAntiSymmetric = Theorem(
    () |- antiSymmetric(emptySet, a)
  ) {
    have(() |- (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z)) by Tautology.from(emptySetAxiom of (x -> pair(y, z)))
    thenHave(() |- forall(z, (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z))) by RightForall
    val ansymCond = thenHave(() |- forall(y, forall(z, (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z)))) by RightForall

    have(thesis) by Tautology.from(antiSymmetric.definition of (r -> emptySet, x -> a), emptySetRelation of (b -> a), ansymCond)
  }

  /**
   * Theorem --- the empty relation is asymmetric.
   */
  val emptyRelationAsymmetric = Theorem(
    () |- asymmetric(emptySet, a)
  ) {
    have(() |- in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet)) by Tautology.from(emptySetAxiom of (x -> pair(y, z)))
    thenHave(() |- forall(z, in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet))) by RightForall
    val asymCond = thenHave(() |- forall(y, forall(z, in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet)))) by RightForall

    have(thesis) by Tautology.from(asymmetric.definition of (r -> emptySet, x -> a), emptySetRelation of (b -> a), asymCond)
  }

  /**
   * Theorem --- the empty relation is total on the empty set.
   */
  val emptyRelationTotalOnItself = Theorem(
    () |- total(emptySet, emptySet)
  ) {
    have((in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z))) by Tautology.from(emptySetAxiom of x -> y)
    thenHave(forall(z, (in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z)))) by RightForall
    thenHave(forall(y, forall(z, (in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z))))) by RightForall

    have(thesis) by Tautology.from(lastStep, total.definition of (r -> emptySet, x -> emptySet), emptySetRelationOnItself)
  }

  // smaller needed lemmas
  // f from x to y => range f <= y
  // f from x to y => dom f = x
  // x <= y, y <= x |- x = y

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
    thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ subset(y, x)) by Substitution.ApplyRules(subsetAxiom)
    thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ forall(t, in(t, y) ==> in(t, x))) by Substitution.ApplyRules(subsetAxiom)
    andThen(Substitution.applySubst(universalConjunctionCommutation of (P -> lambda(t, in(t, x) ==> in(t, y)), Q -> lambda(t, in(t, y) ==> in(t, x)))))
    andThen(Substitution.applySubst(extensionalityAxiom))
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- a set containing only pairs is a relation, and vice versa.
   *
   *    `(\forall t \in z. \exists a, b. t = (a, b)) <=> relation(z)`
   *
   * The domain and codomain of this relation can be obtained constructively by applying
   * the [[replacementSchema]] with the [[firstInPair]] and [[secondInPair]] projection
   * functions.
   *
   * Here, it is sufficient to deal with them abstractly through the definitions of
   * [[relationDomain]] and [[relationRange]].
   */
  val setOfPairsIsRelation = Theorem(
    forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) <=> relation(z)
  ) {
    // if the set contains only pairs, it is a relation
    val fwd = have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) ==> relation(z)) subproof {
      val dom = relationDomain(z)
      val ran = relationRange(z)

      val inst = have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- (in(t, z) ==> exists(a, exists(b, (t === pair(a, b)))))) by InstantiateForall

      // unfold defs
      have(forall(t, in(t, dom) <=> exists(a, in(pair(t, a), z)))) by InstantiateForall(dom)(relationDomain.definition of r -> z)
      val inDom = thenHave((in(a, dom) <=> exists(b, in(pair(a, b), z)))) by InstantiateForall(a)
      have(forall(t, in(t, ran) <=> exists(a, in(pair(a, t), z)))) by InstantiateForall(ran)(relationRange.definition of r -> z)
      val inRan = thenHave((in(b, ran) <=> exists(a, in(pair(a, b), z)))) by InstantiateForall(b)

      have((in(t, z)) |- in(t, z)) by Restate
      val abz = thenHave((in(t, z), (t === pair(a, b))) |- in(pair(a, b), z)) by Substitution.ApplyRules(t === pair(a, b))

      val exa = have((in(t, z), (t === pair(a, b))) |- exists(a, in(pair(a, b), z))) by RightExists(abz)
      val exb = have((in(t, z), (t === pair(a, b))) |- exists(b, in(pair(a, b), z))) by RightExists(abz)

      have((in(t, z), (t === pair(a, b))) |- (t === pair(a, b)) /\ in(a, dom) /\ in(b, ran)) by Tautology.from(exa, exb, inDom, inRan)
      thenHave((in(t, z), (t === pair(a, b))) |- exists(b, (t === pair(a, b)) /\ in(a, dom) /\ in(b, ran))) by RightExists
      thenHave((in(t, z), (t === pair(a, b))) |- exists(a, exists(b, (t === pair(a, b)) /\ in(a, dom) /\ in(b, ran)))) by RightExists

      have((in(t, z), (t === pair(a, b))) |- in(t, cartesianProduct(dom, ran))) by Tautology.from(lastStep, elemOfCartesianProduct of (x -> dom, y -> ran))
      thenHave((in(t, z), exists(b, t === pair(a, b))) |- in(t, cartesianProduct(dom, ran))) by LeftExists
      thenHave((in(t, z), exists(a, exists(b, t === pair(a, b)))) |- in(t, cartesianProduct(dom, ran))) by LeftExists

      have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- in(t, z) ==> in(t, cartesianProduct(dom, ran))) by Tautology.from(lastStep, inst)
      thenHave(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- forall(t, in(t, z) ==> in(t, cartesianProduct(dom, ran)))) by RightForall

      have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- relationBetween(z, dom, ran)) by Tautology.from(
        lastStep,
        subsetAxiom of (x -> z, y -> cartesianProduct(dom, ran)),
        relationBetween.definition of (r -> z, a -> dom, b -> ran)
      )
      thenHave(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- exists(b, relationBetween(z, dom, b))) by RightExists
      thenHave(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- exists(a, exists(b, relationBetween(z, a, b)))) by RightExists

      have(thesis) by Tautology.from(lastStep, relation.definition of r -> z)
    }

    // if the set is a relation, it contains only pairs
    val bwd = have(relation(z) ==> forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b)))))) subproof {
      have(subset(z, cartesianProduct(c, d)) |- forall(t, in(t, z) ==> in(t, cartesianProduct(c, d)))) by Weakening(subsetAxiom of (x -> z, y -> cartesianProduct(c, d)))
      val tz = thenHave(subset(z, cartesianProduct(c, d)) |- (in(t, z) ==> in(t, cartesianProduct(c, d)))) by InstantiateForall(t)

      have(in(t, cartesianProduct(c, d)) |- exists(a, exists(b, (t === pair(a, b))))) subproof {
        have(((t === pair(a, b)) /\ in(a, c) /\ in(a, b)) ==> (t === pair(a, b))) by Restate
        thenHave(forall(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b)) ==> (t === pair(a, b)))) by RightForall
        have(exists(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b))) ==> exists(b, (t === pair(a, b)))) by Cut(
          lastStep,
          existentialImplicationDistribution of (P -> lambda(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b))), Q -> lambda(b, (t === pair(a, b))))
        )
        thenHave(forall(a, exists(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b))) ==> exists(b, (t === pair(a, b))))) by RightForall
        val elemCart = have(exists(a, exists(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b)))) ==> exists(a, exists(b, (t === pair(a, b))))) by Cut(
          lastStep,
          existentialImplicationDistribution of (P -> lambda(a, exists(b, (t === pair(a, b)) /\ in(a, c) /\ in(a, b))), Q -> lambda(a, exists(b, t === pair(a, b))))
        )

        // TODO: Tautology bug
        have(thesis) by Tautology.from(lastStep, elemOfCartesianProduct of (x -> c, y -> d, z -> t))
      }

      have(relationBetween(z, c, d) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by Tautology.from(lastStep, tz, relationBetween.definition of (r -> z, a -> c, b -> d))
      thenHave(exists(d, relationBetween(z, c, d)) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by LeftExists
      thenHave(exists(c, exists(d, relationBetween(z, c, d))) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by LeftExists

      have(relation(z) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by Tautology.from(lastStep, relation.definition of r -> z)
      thenHave(relation(z) |- forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b)))))) by RightForall
      thenHave(thesis) by Restate
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

  /**
   * Theorem --- the union of a set of relations is a relation itself.
   *
   *    `\forall t \in z. relation(t) |- relation(union(z))`
   *
   * This implication also holds in the other direction, but that is
   * not as useful.
   */
  val unionOfRelationSet = Theorem(
    forall(t, in(t, z) ==> relation(t)) |- relation(union(z))
  ) {
    // union of a set of relations contains only pairs
    have(forall(t, in(t, z) ==> relation(t)) |- forall(t, in(t, union(z)) ==> exists(a, exists(b, (t === pair(a, b)))))) subproof {
      assume(forall(t, in(t, z) ==> relation(t)))
      have(in(x, z) ==> relation(x)) by InstantiateForall
      have(in(x, z) |- forall(t, in(t, x) ==> exists(a, exists(b, (t === pair(a, b)))))) by Tautology.from(lastStep, setOfPairsIsRelation of z -> x)
      thenHave((in(x, z) /\ in(t, x)) |- exists(a, exists(b, (t === pair(a, b))))) by InstantiateForall(t)
      thenHave(exists(x, in(x, z) /\ in(t, x)) |- exists(a, exists(b, (t === pair(a, b))))) by LeftExists

      have(in(t, union(z)) ==> exists(a, exists(b, (t === pair(a, b))))) by Tautology.from(lastStep, unionAxiom of (x -> z, z -> t))
      thenHave(thesis) by RightForall
    }

    // a set of pairs is a relation
    have(thesis) by Tautology.from(lastStep, setOfPairsIsRelation of z -> union(z))
  }

  /**
   * Theorem --- Domain of Relational Union
   *
   * If the unary union of a set is relational, then its domain is defined
   * precisely by the union of the domains of its elements.
   *
   *    relation(\cup z) |- \forall t. t \in dom(U z) <=> \exists y \in z. t \in
   *    dom(y)
   *
   * This holds, particularly, as the elements of z must be relations
   * themselves, which follows from the assumption.
   */
  val domainOfRelationalUnion = Theorem(
    relation(union(z)) |- forall(t, in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y))))
  ) {
    val uz = union(z)

    have(forall(t, in(t, relationDomain(uz)) <=> exists(a, in(pair(t, a), uz)))) by InstantiateForall(relationDomain(uz))(relationDomain.definition of r -> uz)
    val inDom = thenHave(in(t, relationDomain(uz)) <=> exists(a, in(pair(t, a), uz))) by InstantiateForall(t)

    assume(relation(uz)) // proof assumption

    have(exists(a, in(pair(t, a), uz)) <=> exists(y, in(y, z) /\ in(t, relationDomain(y)))) subproof {
      // we prove the directions separately
      val fwd = have(exists(a, in(pair(t, a), uz)) |- exists(y, in(y, z) /\ in(t, relationDomain(y)))) subproof {
        have(in(pair(t, a), uz) |- exists(y, in(y, z) /\ in(t, relationDomain(y)))) subproof {
          assume(in(pair(t, a), uz))
          // since \cup z is a union
          // \exists y such that (t, a) \in y
          // and so t \in dom y
          val exy = have(exists(y, in(pair(t, a), y) /\ in(y, z))) by Tautology.from(unionAxiom of (z -> pair(t, a), x -> z))

          have(exists(y, in(pair(t, a), y) /\ in(y, z)) |- exists(y, in(t, relationDomain(y)) /\ in(y, z))) subproof {
            have(forall(z, (z === relationDomain(y)) <=> forall(t, in(t, z) <=> exists(a, in(pair(t, a), y))))) by Weakening(relationDomain.definition of r -> y)
            thenHave(forall(t, in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y)))) by InstantiateForall(relationDomain(y))
            val inDomY = thenHave(in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y))) by InstantiateForall(t)
            have(in(pair(t, a), y) |- in(pair(t, a), y)) by Hypothesis
            thenHave(in(pair(t, a), y) |- exists(a, in(pair(t, a), y))) by RightExists
            have(in(pair(t, a), y) /\ in(y, z) |- in(t, relationDomain(y)) /\ in(y, z)) by Tautology.from(lastStep, inDomY)
            thenHave(in(pair(t, a), y) /\ in(y, z) |- exists(y, in(t, relationDomain(y)) /\ in(y, z))) by RightExists
            thenHave(thesis) by LeftExists
          }

          have(thesis) by Cut(exy, lastStep)
        }

        thenHave(thesis) by LeftExists
      }
      val bwd = have(exists(y, in(y, z) /\ in(t, relationDomain(y))) |- exists(a, in(pair(t, a), uz))) subproof {
        have(in(y, z) /\ in(t, relationDomain(y)) |- exists(a, in(pair(t, a), uz))) subproof {
          assume(in(y, z) /\ in(t, relationDomain(y)))
          have(forall(z, (z === relationDomain(y)) <=> forall(t, in(t, z) <=> exists(a, in(pair(t, a), y))))) by Weakening(relationDomain.definition of r -> y)
          thenHave(forall(t, in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y)))) by InstantiateForall(relationDomain(y))
          thenHave(in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y))) by InstantiateForall(t)
          val exA = thenHave(exists(a, in(pair(t, a), y))) by Tautology

          have(exists(a, in(pair(t, a), y)) |- exists(a, in(pair(t, a), uz))) subproof {
            have(in(pair(t, a), y) |- in(pair(t, a), y) /\ in(y, z)) by Restate
            thenHave(in(pair(t, a), y) |- exists(y, in(pair(t, a), y) /\ in(y, z))) by RightExists
            have(in(pair(t, a), y) |- in(pair(t, a), uz)) by Tautology.from(lastStep, unionAxiom of (z -> pair(t, a), x -> z))
            thenHave(in(pair(t, a), y) |- exists(a, in(pair(t, a), uz))) by RightExists
            thenHave(thesis) by LeftExists
          }

          have(exists(a, in(pair(t, a), uz))) by Cut(exA, lastStep)
        }
        thenHave(thesis) by LeftExists
      }

      have(thesis) by Tautology.from(fwd, bwd)
    }

    have(in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y)))) by Tautology.from(inDom, lastStep)
    thenHave(thesis) by RightForall
  }

}
