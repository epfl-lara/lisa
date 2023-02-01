package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.proven.mathematics.Jechcercises
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
object SetTheory2 extends lisa.Main {

  // var defs
  private val w = variable
  private val x = variable
  private val y = variable
  private val z = variable
  private val t = variable
  private val a = variable
  private val b = variable
  private val c = variable

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
    andThen(forall(y, !in(y, y) <=> in(y, x)) |- ()) by LeftForall(x)
    andThen(exists(x, forall(y, !in(y, y) <=> in(y, x))) |- ()) by LeftExists
  }
  show

  /**
   * Theorem --- No Universal Set
   *
   * There does not exist a set of all sets. Alternatively, its existence, with
   * the comprehension schema and Russel's paradox, produces a contradiction.
   */
  val noUniversalSet = makeTHM(
    forall(z, in(z, x)) |- ()
  ) {
    have(in(x, x) |- ()) by Rewrite(Jechcercises.selfNonInclusion)
    andThen(forall(z, in(z, x)) |- ()) by LeftForall(x)
  }
  show

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
  val uniquenessByDefinition = makeTHM(
    exists(z, forall(t, in(t, z) <=> schemPred(t))) |- existsOne(z, forall(t, in(t, z) <=> schemPred(t)))
  ) {
    def prop(z: Term) = in(t, z) <=> schemPred(t)
    def fprop(z: Term) = forall(t, prop(z))

    // forward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    andThen(fprop(z) /\ (z === a) |- fprop(z)) by Weakening
    andThen(Set(fprop(z) /\ (z === a), (z === a)) |- fprop(a)) by RightSubstEq(List((z, a)), lambda(Seq(z), fprop(z)))
    val forward = andThen(fprop(z) |- (z === a) ==> fprop(a)) by Restate

    // backward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    val instLhs = andThen(fprop(z) |- prop(z)) by InstantiateForall(t)
    val instRhs = andThen(fprop(a) |- prop(a)) by InstFunSchema(Map(z -> a))

    have(Set(fprop(z), fprop(a)) |- prop(z) /\ prop(a)) by RightAnd(instLhs, instRhs)
    andThen(fprop(z) /\ fprop(a) |- in(t, a) <=> in(t, z)) by Trivial
    val extLhs = andThen(fprop(z) /\ fprop(a) |- forall(t, in(t, a) <=> in(t, z))) by RightForall
    val extRhs = have(() |- forall(t, in(t, a) <=> in(t, z)) <=> (a === z)) by InstFunSchema(Map(x -> a, y -> z))(extensionalityAxiom)

    have(fprop(z) /\ fprop(a) |- (forall(t, in(t, a) <=> in(t, z)) <=> (a === z)) /\ forall(t, in(t, a) <=> in(t, z))) by RightAnd(extLhs, extRhs)
    andThen(fprop(z) /\ fprop(a) |- (a === z)) by Trivial
    val backward = andThen(fprop(z) |- fprop(a) ==> (a === z)) by Restate

    have(fprop(z) |- fprop(a) <=> (a === z)) by RightIff(forward, backward)
    andThen(fprop(z) |- forall(a, fprop(a) <=> (a === z))) by RightForall
    andThen(fprop(z) |- exists(z, forall(a, fprop(a) <=> (a === z)))) by RightExists(z)
    andThen(exists(z, fprop(z)) |- exists(z, forall(a, fprop(a) <=> (a === z)))) by LeftExists
    andThen(exists(z, fprop(z)) |- existsOne(z, fprop(z))) by RightExistsOne
  }
  show

  /**
   * Theorem Schema --- Unique Comprehension
   *
   * Given a set `x`, and a predicate `P(t, x)`, comprehension postulates there
   * is a set containing the elements `t` of `x` satisfying `P(t, x)`. This set
   * is unique by extensionality.
   *
   *    `() ⊢ ∃! z. ∀ t. t ∈ z ⇔ (t ∈ x ⋀ P(t, x))`
   *
   * @param originalSet the set to apply comprehension on
   * @param separationPredicate the predicate to use for comprehension `(Term =>
   * Term => Boolean)`
   * @return pair (existence, uniqueness) of theorems of the respective
   * properties
   *
   * @example 
   * Generates proofs for the unique existence of the set `{t ∈ x | t ∈ y}`.
   * {{{
   * val (existence, uniqueness) = uniqueComprehension(x, lambda(Seq(t, x), in(t, y))) 
   * }}}
   * See [[setIntersection]] or [[relationDomain]] for more usage.
   */
  def uniqueComprehension(originalSet: Term, separationPredicate: LambdaTermFormula) = {
    require(separationPredicate.vars.length == 2) // separationPredicate takes two args

    // fresh variable names to avoid conflicts
    val t1 = VariableLabel(freshId(separationPredicate.body.freeVariables.map(_.id) ++ originalSet.freeVariables.map(_.id), x.id))
    val t2 = VariableLabel(freshId(separationPredicate.body.freeVariables.map(_.id) ++ originalSet.freeVariables.map(_.id), y.id))

    val existence = makeTHM(
      () |- exists(t1, forall(t2, in(t2, t1) <=> (in(t2, originalSet) /\ separationPredicate(Seq(t2, originalSet)))))
    ) {
      have(() |- exists(t1, forall(t2, in(t2, t1) <=> (in(t2, z) /\ sPhi(t2, z))))) by Rewrite(comprehensionSchema)
      andThen(() |- exists(t1, forall(t2, in(t2, t1) <=> (in(t2, originalSet) /\ sPhi(t2, originalSet))))) by InstFunSchema(Map(z -> originalSet))
      andThen(() |- exists(t1, forall(t2, in(t2, t1) <=> (in(t2, originalSet) /\ separationPredicate(Seq(t2, originalSet)))))) by InstPredSchema(
        Map(sPhi -> lambda(Seq(t1, t2), separationPredicate(Seq(t1, t2))))
      )
    }

    val uniqueness = makeTHM(
      () |- existsOne(t1, forall(t2, in(t2, t1) <=> (in(t2, originalSet) /\ separationPredicate(Seq(t2, originalSet)))))
    ) {
      val prop = (in(t2, originalSet) /\ separationPredicate(Seq(t2, originalSet)))
      def fprop(z: Term) = forall(t2, in(t2, z) <=> prop)

      val existsRhs = have(exists(t1, fprop(t1)) |- existsOne(t1, fprop(t1))) by InstPredSchema(Map(schemPred -> (t2, prop)))(uniquenessByDefinition)

      // assumption elimination
      // in essence, an existence proof
      val existsLhs = have(() |- exists(t1, fprop(t1))) by Rewrite(existence)

      have(() |- existsOne(t1, fprop(t1))) by Cut(existsLhs, existsRhs)
    }

    (existence, uniqueness)
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
      andThen(() |- ((successor(y) === successor(y)) <=> (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))))) by InstantiateForall(successor(y))
      val succDef = andThen(() |- (successor(y) === union(unorderedPair(y, unorderedPair(y, y))))) by Rewrite
      val inductDef = have(() |- inductive(x) <=> in(emptySet(), x) /\ forall(y, in(y, x) ==> in(successor(y), x))) by Rewrite(inductive.definition)

      have(() |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Restate
      val succEq = andThen(
        (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(successor(y), x))
      ) by RightSubstEq(
        List((successor(y), union(unorderedPair(y, unorderedPair(y, y))))),
        lambda(z, (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(z, x)))
      )
      val iffinst = have(() |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (in(y, x) ==> in(successor(y), x))) by Cut(succDef, succEq)

      val iffquant = {
        have((in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (in(y, x) ==> in(successor(y), x))) by Weakening(iffinst)
        andThen(forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (in(y, x) ==> in(successor(y), x))) by LeftForall(y)
        andThen(forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- forall(y, in(y, x) ==> in(successor(y), x))) by RightForall
        val lhs = andThen(() |- forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) ==> forall(y, in(y, x) ==> in(successor(y), x))) by Rewrite

        have((in(y, x) ==> in(successor(y), x)) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Weakening(iffinst)
        andThen(forall(y, in(y, x) ==> in(successor(y), x)) |- (in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by LeftForall(y)
        andThen(forall(y, in(y, x) ==> in(successor(y), x)) |- forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by RightForall
        val rhs = andThen(() |- forall(y, in(y, x) ==> in(successor(y), x)) ==> forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Rewrite

        have(() |- forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> forall(y, in(y, x) ==> in(successor(y), x))) by RightIff(lhs, rhs)
      }

      have(
        in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- in(emptySet(), x) /\ forall(
          y,
          in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)
        )
      ) by Hypothesis
      andThen(
        Set(
          forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> forall(y, in(y, x) ==> in(successor(y), x)),
          in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
        ) |- in(emptySet(), x) /\ forall(y, in(y, x) ==> in(successor(y), x))
      ) by RightSubstIff(
        List((forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)), forall(y, in(y, x) ==> in(successor(y), x)))),
        lambda(form, in(emptySet(), x) /\ form)
      )
      val substituted = andThen(
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

      andThen(Set(in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) |- exists(x, inductive(x))) by RightExists(x)
      val rhs = andThen(Set(exists(x, in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)))) |- exists(x, inductive(x))) by LeftExists

      have(() |- exists(x, inductive(x))) by Cut(infinityAxiom, rhs)
    }
    show

    ////////////////////////////////////////////////////////////////////////////

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
    val rhs = andThen((z === x) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === x) |- (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    andThen((z === x) |- in(z, unorderedPair(x, y))) by Trivial
    andThen((x === x) |- in(x, unorderedPair(x, y))) by InstFunSchema(Map(z -> x))
    andThen(() |- in(x, unorderedPair(x, y))) by LeftRefl
  }
  show

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
    val rhs = andThen((z === y) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === y) |- (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    andThen((z === y) |- in(z, unorderedPair(x, y))) by Trivial
    andThen((y === y) |- in(y, unorderedPair(x, y))) by InstFunSchema(Map(z -> y))
    andThen(() |- in(y, unorderedPair(x, y))) by LeftRefl
  }
  show

  // val unionOfOrderedPairIsUnordered = makeTHM(
  //   () |- union(pair(x, y)) === unorderedPair(x, y)
  // ) {
  //   val upAxiom = ax"unorderedPair"

  //   /**
  //    * strategy
  //    * prove:
  //    *    lhs
  //    *    () |- z in uPair(x, y) <=> z is x or z is y
  //    *    rhs
  //    *    () |- z in oPair(x, y) <=> z is x or z is y
  //    *
  //    * derive z in uPair(x, y) <=> z in oPair(x, y) and apply extensionality
  //    */

  //   // val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by Instantiateforall(x, y, z)(upAxiom)

  // }

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
    andThen(in(z, union(X)) |- exists(y, in(z, y) /\ in(y, X))) by Trivial

    val andLhs = have(() |- in(x, X)) by InstFunSchema(Map(y -> x))(firstElemInPair)
    val andRhs = have(in(z, x) |- in(z, x)) by Hypothesis
    have(in(z, x) |- in(z, x) /\ in(x, X)) by RightAnd(andLhs, andRhs)
    val fwdLhs = andThen(in(z, x) |- exists(y, in(z, y) /\ in(y, X))) by RightExists(x)
    have(in(z, x) |- exists(y, in(z, y) /\ in(y, X)) /\ (in(z, union(X)) <=> exists(y, in(z, y) /\ in(y, X)))) by RightAnd(fwdLhs, unionAx)
    andThen(in(z, x) |- in(z, union(X))) by Trivial
    val fwd = andThen(() |- in(z, x) ==> in(z, union(X))) by Rewrite

    // backward direction
    //  z ∈ ∪ X |- z ∈ x

    have(in(y, X) |- in(y, X)) by Hypothesis
    val bwdHypo = andThen(in(z, y) /\ in(y, X) |- in(y, X)) by Weakening
    have(in(z, y) /\ in(y, X) |- in(y, X) /\ (in(y, X) <=> (x === y))) by RightAnd(bwdHypo, Jechcercises.singletonHasNoExtraElements)
    val cutLhs = andThen(in(z, y) /\ in(y, X) |- (x === y)) by Trivial

    have(in(z, y) |- in(z, y)) by Hypothesis
    andThen(in(y, X) /\ in(z, y) |- in(z, y)) by Weakening
    val cutRhs = andThen(Set(in(z, y) /\ in(y, X), (x === y)) |- in(z, x)) by RightSubstEq(List((y, x)), lambda(y, in(z, y)))

    have(in(z, y) /\ in(y, X) |- in(z, x)) by Cut(cutLhs, cutRhs)
    val bwdRhs = andThen(exists(y, in(z, y) /\ in(y, X)) |- in(z, x)) by LeftExists
    val bwdLhs = have(in(z, union(X)) |- exists(y, in(z, y) /\ in(y, X))) by Weakening(unionAx)
    have(in(z, union(X)) |- in(z, x)) by Cut(bwdLhs, bwdRhs)
    val bwd = andThen(() |- in(z, union(X)) ==> in(z, x)) by Rewrite

    have(() |- in(z, union(X)) <=> in(z, x)) by RightIff(fwd, bwd)
    val iff = andThen(() |- forall(z, in(z, union(X)) <=> in(z, x))) by RightForall

    val extAx = have(() |- forall(z, in(z, union(X)) <=> in(z, x)) <=> (union(X) === x)) by InstFunSchema(Map(x -> union(X), y -> x))(extensionalityAxiom)

    have(() |- forall(z, in(z, union(X)) <=> in(z, x)) /\ (forall(z, in(z, union(X)) <=> in(z, x)) <=> (union(X) === x))) by RightAnd(iff, extAx)
    andThen(() |- (union(X) === x)) by Trivial
  }
  show

  //////////////////////////////////////////////////////////////////////////////

  /**
    * Operations on Sets
    */

  val (setIntersectionExistence, setIntersectionUniqueness) = uniqueComprehension(x, lambda(Seq(t, z), in(t, y)))

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

  val (unaryIntersectionExistence, unaryIntersectionUniqueness) = uniqueComprehension(union(x), lambda(Seq(t, z), forall(b, in(b, x) ==> in(t, b))))

  /**
    * Unary Set Intersection --- Intersection of all elements of a given set.
    *
    *     `∩ x = {z ∈ ∪ x | ∀ y ∈ x. z ∈ y}`
    *
    * The proofs are guaranteed and generated by [[uniqueComprehension]].
    *
    * @param x set
    */
  val unaryintersection = DEF(x) -> The(z, forall(t, in(t, z) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))(unaryIntersectionUniqueness)

  val (setDifferenceExistence, setDifferenceUniqueness) = uniqueComprehension(x, lambda(Seq(t, z), !in(t, y)))

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
    val conjunction = andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, x), forall(y, P(y) ==> in(t, y)))))

    have(forall(y, P(y) ==> in(t, y)) |- forall(y, P(y) ==> in(t, y))) by Hypothesis
    andThen(forall(y, P(y) ==> in(t, y)) /\ P(x) |- forall(y, P(y) ==> in(t, y))) by Weakening
    andThen(forall(y, P(y) ==> in(t, y)) /\ P(x) |- P(x) ==> in(t, x)) by InstantiateForall(x)
    andThen(forall(y, P(y) ==> in(t, y)) /\ P(x) |- in(t, x) /\ forall(y, P(y) ==> in(t, y))) by Trivial
    val fwd = andThen(P(x) |- forall(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Rewrite

    have((in(t, x) /\ forall(y, P(y) ==> in(t, y))) |- (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Hypothesis
    val bwd = andThen(() |- (in(t, x) /\ forall(y, P(y) ==> in(t, y))) ==> (forall(y, P(y) ==> in(t, y)))) by Rewrite

    val lhs = have(P(x) |- forall(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by RightIff(fwd, bwd)

    val form = formulaVariable
    have((in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) |- in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Hypothesis
    val rhs = andThen(
      Set((in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))), (forall(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))) |- (in(t, z) <=> (forall(y, P(y) ==> in(t, y))))
    ) by RightSubstIff(List((forall(y, P(y) ==> in(t, y)), (in(t, x) /\ forall(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))

    have(Set(P(x), (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))) |- in(t, z) <=> (forall(y, P(y) ==> in(t, y)))) by Cut(lhs, rhs)
    andThen(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- in(t, z) <=> (forall(y, P(y) ==> in(t, y)))) by LeftForall(t)
    andThen(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y))))) by RightForall
    andThen(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by RightExists(z)
    val cutRhs = andThen(Set(P(x), exists(z, forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))))) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by LeftExists

    have(P(x) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by Cut(conjunction, cutRhs)
    andThen(exists(x, P(x)) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by LeftExists

  }
  show

  /**
   * Cartesian Products and Relations
   */

  val (cartesianProductExistence, cartesianProductUniqueness) =
    uniqueComprehension(powerSet(setUnion(x, y)), lambda(Seq(t, z), exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y)))))

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

  val (relationDomainExistence, relationDomainUniqueness) = uniqueComprehension(union(union(r)), lambda(Seq(t, b), exists(a, in(pair(t, a), r))))

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

  val (relationRangeExistence, relationRangeUniqueness) = uniqueComprehension(union(union(r)), lambda(Seq(t, b), exists(a, in(pair(a, t), r))))

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

  val (restrictedFunctionExistence, restrictedFunctionUniqueness) = uniqueComprehension(f, lambda(Seq(t, b), exists(y, exists(z, in(y, x) /\ (t === pair(y, z))))))

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

  val (piExistence, piUniqueness) = uniqueComprehension(powerSet(Sigma(x, f)), lambda(Seq(z, y), (subset(x, relationDomain(z)) /\ functional(z))))

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
  show

  /**
   *
   * Theorem --- The intersection of all inductive sets is unique
   */
  val inductiveIntersectionUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> forall(y, inductive(y) ==> in(t, y))))
  ) {
    val prop = forall(y, inductive(y) ==> in(t, y))
    val fprop = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop) |- existsOne(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)
    val existsLhs = have(() |- exists(z, fprop)) by Rewrite(inductiveIntersectionExistence)

    have(() |- existsOne(z, fprop)) by Cut(existsLhs, existsRhs)
  }
  show

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
    val inductEmpty = andThen(() |- forall(x, inductive(x) ==> in(emptySet(), x))) by RightForall

    val defEmpty =
      have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(emptySet(), z) <=> (forall(x, inductive(x) ==> in(emptySet(), x))))) by InstantiateForall(emptySet())(defHypo)

    have(
      forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(emptySet(), z) <=> (forall(x, inductive(x) ==> in(emptySet(), x)))) /\ forall(x, inductive(x) ==> in(emptySet(), x))
    ) by RightAnd(defEmpty, inductEmpty)
    val baseCase = andThen(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- in(emptySet(), z)) by Trivial

    // if y in N, then succ y in N
    have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) by InstantiateForall(t)(defHypo)
    andThen(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) by Weakening
    andThen(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (forall(x, inductive(x) ==> in(t, x)))) by Trivial
    andThen(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (inductive(x) ==> in(t, x))) by InstantiateForall(x)
    val inInductive = andThen(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x)) by Restate

    have(inductive(x) |- forall(t, in(t, x) ==> in(successor(t), x))) by Weakening(inductive.definition)
    val inInductiveDef = andThen(inductive(x) |- in(t, x) ==> in(successor(t), x)) by InstantiateForall(t)

    have(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x) /\ (in(t, x) ==> in(successor(t), x))) by RightAnd(inInductive, inInductiveDef)
    andThen(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(successor(t), x)) by Trivial
    andThen(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- inductive(x) ==> in(successor(t), x)) by Restate
    val succInst = andThen(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- forall(x, inductive(x) ==> in(successor(t), x))) by RightForall

    val nDefSucc =
      have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(successor(t), z) <=> (forall(x, inductive(x) ==> in(successor(t), x))))) by InstantiateForall(successor(t))(defHypo)
    have(
      Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- forall(x, inductive(x) ==> in(successor(t), x)) /\ (in(successor(t), z) <=> (forall(
        x,
        inductive(x) ==> in(successor(t), x)
      )))
    ) by RightAnd(succInst, nDefSucc)
    andThen(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- in(successor(t), z)) by Trivial
    andThen(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) |- in(t, z) ==> in(successor(t), z)) by Restate
    val inductiveCase = andThen(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- forall(t, in(t, z) ==> in(successor(t), z))) by RightForall

    have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- in(emptySet(), z) /\ forall(t, in(t, z) ==> in(successor(t), z))) by RightAnd(baseCase, inductiveCase)

    val form = formulaVariable
    val inductIff = andThen(
      Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), inductive(z) <=> (in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))) |- inductive(z)
    ) by RightSubstIff(List((inductive(z), in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))), lambda(form, form))

    val inductDef = have(() |- inductive(z) <=> (in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))) by InstFunSchema(Map(x -> z))(inductive.definition)

    have(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) |- inductive(z)) by Cut(inductDef, inductIff)
    val inductExpansion =
      andThen(Set(forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) |- inductive(naturalsInductive())) by InstFunSchema(Map(z -> naturalsInductive()))

    have(() |- (naturalsInductive() === naturalsInductive()) <=> forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) by InstantiateForall(naturalsInductive())(
      naturalsInductive.definition
    )
    val natDef = andThen(() |- forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) by Rewrite

    have(() |- inductive(naturalsInductive())) by Cut(natDef, inductExpansion)
  }
  show

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

  val setOfLowerBounds = DEF(y, r, x) --> The(z, forall(t, in(t, z) <=> (in(t, x) /\ lowerBound(t, y, r, x))))(uniqueComprehension(x, lambda(Seq(t, x), lowerBound(t, y, r, x)))._2)
}
