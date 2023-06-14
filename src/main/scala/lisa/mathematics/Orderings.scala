package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.FirstOrderLogic.*
import lisa.mathematics.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.utils.FOLPrinter

object Orderings extends lisa.Main {

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
  private val F = function(1)
  private val G = function(2)

  private val P = predicate(1)
  private val Q = predicate(1)
  private val schemPred = predicate(1)

  /**
   * Linear and Partial Ordering
   */

  /**
   * (Strict) Partial Order --- `p` is a partial order on `x` if it is a pair `(x, r)`,
   * and `r` is an [[antiReflexive]], [[antiSymmetric]], and [[transitive]] binary
   * [[relation]] on `x`.
   */
  val partialOrder =
    DEF(p) --> relationBetween(secondInPair(p), firstInPair(p), firstInPair(p)) /\ antiSymmetric(secondInPair(p), firstInPair(p)) /\ antiReflexive(secondInPair(p), firstInPair(p)) /\ transitive(
      secondInPair(p),
      firstInPair(p)
    )

  /**
   * Linear Order --- a partial order `p = (r, x)` is called a linear order if
   * `r` is [[total]] as a [[relation]] on `x`.
   */
  val totalOrder = DEF(p) --> partialOrder(p) /\ total(secondInPair(p), firstInPair(p))

  /**
   * Properties of elements under partial orders
   */

  /**
   * Maximal Element --- `a` is a maximal element of `y` with respect to `r`,
   * where `p = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. ! a r b`
   */
  val maximalElement = DEF(a, y, p) --> partialOrder(p) /\ subset(y, firstInPair(p)) /\ in(a, y) /\ ∀(b, in(b, y) ==> (!in(pair(a, b), secondInPair(p))))

  /**
   * Minimal Element --- `a` is a minimal element of `y` with respect to `r`,
   * where `p = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. ! b r a`
   */
  val minimalElement = DEF(a, y, p) --> partialOrder(p) /\ subset(y, firstInPair(p)) /\ in(a, y) /\ ∀(b, in(b, y) ==> (!in(pair(b, a), secondInPair(p))))

  /**
   * Greatest Element --- `a` is the greatest element of `y` with respect to
   * `r`, where `p = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. b r a ⋁ b = a`
   */
  val greatestElement = DEF(a, y, p) --> partialOrder(p) /\ subset(y, firstInPair(p)) /\ in(a, y) /\ ∀(b, in(b, y) ==> (in(pair(b, a), secondInPair(p)) \/ (a === b)))

  /**
   * Least Element --- `a` is the least element of `y` with respect to `r`,
   * where `p = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. a r b ⋁ b = a`
   */
  val leastElement = DEF(a, y, p) --> partialOrder(p) /\ subset(y, firstInPair(p)) /\ in(a, y) /\ ∀(b, in(b, y) ==> (in(pair(a, b), secondInPair(p)) \/ (a === b)))

  /**
   * Upper Bound --- `a` is an upper bound on `y` with respect to `r`, where `p
   * = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. b r a ⋁ b = a`
   *
   * Note that as opposed to the greatest element, `a` is not enforced to be an
   * element of `y`.
   */
  val upperBound = DEF(a, y, p) --> partialOrder(p) /\ subset(y, firstInPair(p)) /\ ∀(b, in(b, y) ==> (in(pair(b, a), secondInPair(p)) \/ (a === b)))

  /**
   * Lower Bound --- `a` is a lower bound on `y` with respect to `r`, where `p =
   * (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. a r b ⋁ b = a`
   *
   * Note that as opposed to the least element, `a` is not enforced to be an
   * element of `y`
   */
  val lowerBound = DEF(a, y, p) --> partialOrder(p) /\ subset(y, firstInPair(p)) /\ ∀(b, in(b, y) ==> (in(pair(a, b), secondInPair(p)) \/ (a === b)))

  val setOfLowerBoundsUniqueness = Theorem(
    () |- ∃!(z, ∀(t, in(t, z) <=> (in(t, secondInPair(p)) /\ lowerBound(t, y, p))))
  ) {
    have(thesis) by UniqueComprehension(secondInPair(p), lambda(Seq(t, x), lowerBound(t, y, p)))
  }

  /**
   * The set of all lower bounds of a set `y` under a partial order `p`. Used to define [[greatestLowerBound]]
   */
  val setOfLowerBounds = DEF(y, p) --> The(z, ∀(t, in(t, z) <=> (in(t, secondInPair(p)) /\ lowerBound(t, y, p))))(setOfLowerBoundsUniqueness)

  /**
   * Greatest Lower Bound --- `a` is the greatest lower bound on `y ⊆ x`
   * under a partial order `p = (r, x)` if it is the greatest element in the
   * [[setOfLowerBounds]] of `y` under `p`.
   */
  val greatestLowerBound = DEF(a, y, p) --> greatestElement(a, setOfLowerBounds(y, p), p)

  /**
   * Alias for [[greatestLowerBound]]
   */
  val infimum = greatestLowerBound

  val setOfUpperBoundsUniqueness = Theorem(
    () |- ∃!(z, ∀(t, in(t, z) <=> (in(t, secondInPair(p)) /\ upperBound(t, y, p))))
  ) {
    have(thesis) by UniqueComprehension(secondInPair(p), lambda(Seq(t, x), upperBound(t, y, p)))
  }

  /**
   * The set of all upper bounds of a set `y` under a partial order `p`. Used to define [[leastUpperBound]]
   */
  val setOfUpperBounds = DEF(y, p) --> The(z, ∀(t, in(t, z) <=> (in(t, secondInPair(p)) /\ upperBound(t, y, p))))(setOfUpperBoundsUniqueness)

  /**
   * Least Upper Bound --- `a` is the least upper bound on `y ⊆ x` under
   * a partial order `p = (r, x)` if it is the least element in the
   * [[setOfUpperBounds]] of `y` under `p`.
   */
  val greatestUpperBound = DEF(a, y, p) --> leastElement(a, setOfUpperBounds(y, p), p)

  /**
   * Alias for [[greatestUpperBound]]
   */
  val supremum = greatestUpperBound

  /**
   * Properties of functions under partial orders
   */

  /**
   * Order Preserving Function --- a function `f` between `P` and `Q` such that
   * `p = (P, <_p)` and `q = (Q, <_q)` are partially ordered is order-preserving
   * if
   *
   * `∀ x y. x <_p y ⟹ f(x) <_q f(y)`
   */
  val orderPreserving = DEF(f, p, q) --> partialOrder(p) /\ partialOrder(q) /\ functionFrom(f, firstInPair(p), firstInPair(q)) /\ ∀(
    x,
    ∀(y, in(pair(x, y), secondInPair(p)) ==> in(pair(app(f, x), app(f, y)), secondInPair(q)))
  )

  /**
   * Increasing Function --- an order preserving function ([[orderPreserving]])
   * between two partially ordered sets is increasing if the two sets are
   * linearly ordered ([[totalOrder]]).
   */
  val increasing = DEF(f, p, q) --> totalOrder(p) /\ totalOrder(q) /\ orderPreserving(f, p, q)

  /**
   * Isomorphism of Partially Ordered Sets --- a function `f` is an isomorphism
   * between two partially ordered sets `p = (P, <_p)` and `q = (Q, <_q)` if it
   * is an [[injective]] function from `P` to `Q`, and both `f` and `f^-1` are
   * [[orderPreserving]].
   */
  // val isomorphismOfPartialOrders = DEF (f, p, q) --> injective(f, firstInPair(p), firstInPair(q)) /\ orderPreserving(f, p, q) /\ orderPreserving(inverseFunction(f), p, q)

  private val pA = variable // order
  private val pB = variable // order
  val orderIsomorphism = DEF(pA, pB, f) --> {
    val A = firstInPair(pA)
    val B = firstInPair(pB)
    val `<A` = secondInPair(pA)
    val `<B` = secondInPair(pB)
    partialOrder(pA) /\ partialOrder(pB) /\ bijective(f, A, B) /\
      ∀(
        x,
        in(x, A) ==> ∀(
          y,
          in(y, A) ==>
            (in(pair(x, y), `<A`) <=> in(pair(app(f, x), app(f, y)), `<B`)) // f(x) <B f(y)
        )
      )
  }

  val partialOrderSubset = Lemma(
    partialOrder(p) /\ subset(c, firstInPair(p)) /\ subset(d, secondInPair(p)) |- partialOrder(pair(c, d))
  ) {
    assume(partialOrder(p))
    assume(subset(c, firstInPair(p)))
    assume(subset(d, secondInPair(p)))

    sorry
  }

  val inclusionOnUniqueness = Lemma(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))))
  ) {
    have(thesis) by UniqueComprehension(cartesianProduct(a, a), lambda(Seq(t, a), exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))
  }

  /**
   * The relation induced by inclusion on a set, noted `∈_a`.
   *
   * `∈_a = {(y, x) ∈ a * a | y ∈ x}`
   */
  val inclusionOn = DEF(a) --> The(z, forall(t, in(t, z) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))))(inclusionOnUniqueness)

  /**
   * The partial order `(a, ∈_a)` induced by the inclusion relation
   * ([[inclusionOn]]) on a set.
   */
  val inclusionOrderOn = DEF(a) --> pair(a, inclusionOn(a))

  /**
   * Theorem --- the inclusion order on a set is defined by the meta inclusion [[in]].
   */
  val inclusionOrderElem = Lemma(
    () |- (in(b, a) /\ in(c, a) /\ in(b, c)) <=> in(pair(b, c), inclusionOn(a))
  ) {
    val prodElem = have((in(b, a) /\ in(c, a)) <=> in(pair(b, c), cartesianProduct(a, a))) by Restate.from(pairInCartesianProduct of (a -> b, b -> c, x -> a, y -> a))

    val exXY = have(in(b, c) <=> exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x))))) subproof {
      val fwd = have(in(b, c) |- exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x))))) subproof {
        have(in(b, c) |- in(b, c) /\ (pair(b, c) === pair(b, c))) by Restate
        thenHave(in(b, c) |- exists(x, in(b, x) /\ (pair(b, c) === pair(b, x)))) by RightExists
        thenHave(thesis) by RightExists
      }
      val bwd = have(exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x)))) |- in(b, c)) subproof {
        val pairExt = have((pair(b, c) === pair(y, x)) |- (b === y) /\ (c === x)) by Weakening(pairExtensionality of (a -> b, b -> c, c -> y, d -> x))

        have(in(y, x) |- in(y, x)) by Hypothesis
        thenHave((in(y, x), b === y, c === x) |- in(b, c)) by Substitution.apply2(true, b === y, c === x)
        have((in(y, x) /\ (pair(b, c) === pair(y, x))) |- in(b, c)) by Tautology.from(pairExt, lastStep)
        thenHave(exists(x, in(y, x) /\ (pair(b, c) === pair(y, x))) |- in(b, c)) by LeftExists
        thenHave(thesis) by LeftExists
      }

      have(thesis) by Tautology.from(fwd, bwd)
    }

    have(forall(t, in(t, inclusionOn(a)) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(inclusionOn(a))(inclusionOn.definition)
    thenHave(in(pair(b, c), inclusionOn(a)) <=> (in(pair(b, c), cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x)))))) by InstantiateForall(pair(b, c))

    have(thesis) by Tautology.from(lastStep, prodElem, exXY)
  }

  /**
   * Theorem --- the inclusion order on the any set is a relation.
   */
  val inclusionIsRelation = Theorem(
    () |- relationBetween(inclusionOn(a), a, a)
  ) {
    have(forall(t, in(t, inclusionOn(a)) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(inclusionOn(a))(inclusionOn.definition)
    thenHave(in(t, inclusionOn(a)) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))) by InstantiateForall(t)
    thenHave(in(t, inclusionOn(a)) ==> in(t, cartesianProduct(a, a))) by Weakening
    thenHave(forall(t, in(t, inclusionOn(a)) ==> in(t, cartesianProduct(a, a)))) by RightForall
    // thenHave(forall(z, in(z, inclusionOn(a)) ==> in(z, cartesianProduct(a, a)))) by Restate
    val subs = thenHave(subset(inclusionOn(a), cartesianProduct(a, a))) by Substitution.apply2(true, subsetAxiom of (x -> inclusionOn(a), y -> cartesianProduct(a, a)))

    have(thesis) by Tautology.from(subs, relationBetween.definition of (r -> inclusionOn(a), a -> a, b -> a))
  }

  val inclusionIsAntiReflexive = Theorem(
    antiReflexive(inclusionOn(a), a)
  ) {
    sorry
  }

  val inclusionIsAntiSymmetric = Theorem(
    antiSymmetric(inclusionOn(a), a)
  ) {
    sorry
  }

  /**
   * Theorem --- the inclusion order on the empty set is the empty relation.
   */
  val emptySetInclusionEmpty = Lemma(
    () |- (inclusionOn(emptySet()) === emptySet())
  ) {
    have(forall(t, in(t, inclusionOn(emptySet())) <=> (in(t, cartesianProduct(emptySet(), emptySet())) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(
      inclusionOn(emptySet())
    )(inclusionOn.definition of (a -> emptySet()))
    val incDef = thenHave(in(t, inclusionOn(emptySet())) <=> (in(t, cartesianProduct(emptySet(), emptySet())) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))) by InstantiateForall(t)

    have(forall(t, in(t, cartesianProduct(emptySet(), emptySet())) <=> in(t, emptySet()))) by Tautology.from(
      productWithEmptySetEmpty of (x -> emptySet()),
      extensionalityAxiom of (x -> cartesianProduct(emptySet(), emptySet()), y -> emptySet())
    )
    val emp = thenHave(in(t, cartesianProduct(emptySet(), emptySet())) <=> in(t, emptySet())) by InstantiateForall(t)

    val impl = have(in(t, inclusionOn(emptySet())) <=> in(t, emptySet())) subproof {
      val lhs = have(in(t, inclusionOn(emptySet())) |- in(t, emptySet())) by Tautology.from(incDef, emp)
      val rhs = have(in(t, emptySet()) |- in(t, inclusionOn(emptySet()))) by Weakening(emptySet.definition of (x -> t))
      have(thesis) by Tautology.from(lhs, rhs)
    }

    val ext = thenHave(forall(t, in(t, inclusionOn(emptySet())) <=> in(t, emptySet()))) by RightForall
    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x -> inclusionOn(emptySet()), y -> emptySet()))
  }

  /**
   * Theorem --- the inclusion order on the empty set is a reflexive relation.
   */
  val emptyInclusionReflexive = Lemma(
    () |- reflexive(inclusionOn(emptySet()), emptySet())
  ) {
    have(reflexive(emptySet(), emptySet())) by Restate.from(emptyRelationReflexiveOnItself)
    thenHave(thesis) by Substitution.apply2(true, emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is an irreflexive relation.
   */
  val emptyInclusionIrreflexive = Lemma(
    () |- irreflexive(inclusionOn(emptySet()), a)
  ) {
    have(irreflexive(emptySet(), a)) by Restate.from(emptyRelationIrreflexive)
    thenHave(thesis) by Substitution.apply2(true, emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is a transitive relation.
   */
  val emptyInclusionTransitive = Lemma(
    () |- transitive(inclusionOn(emptySet()), a)
  ) {
    have(transitive(emptySet(), a)) by Restate.from(emptyRelationTransitive)
    thenHave(thesis) by Substitution.apply2(true, emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the empty relation partially orders the empty set
   */
  val emptySetPartialOrder = Lemma(
    () |- partialOrder(pair(emptySet(), emptySet()))
  ) {
    have(
      partialOrder(pair(emptySet(), emptySet())) <=> (relationBetween(emptySet(), emptySet(), emptySet()) /\ antiSymmetric(emptySet(), emptySet()) /\ antiReflexive(
        emptySet(),
        emptySet()
      ) /\ transitive(emptySet(), emptySet()))
    ) by Substitution.apply2(false, firstInPairReduction of (x -> emptySet(), y -> emptySet()), secondInPairReduction of (x -> emptySet(), y -> emptySet()))(
      partialOrder.definition of p -> pair(emptySet(), emptySet())
    )
    have(thesis) by Tautology.from(
      lastStep,
      emptySetRelationOnItself,
      emptyRelationIrreflexive of a -> emptySet(),
      emptyRelationTransitive of a -> emptySet(),
      emptyRelationAntiSymmetric of a -> emptySet()
    )
  }

  /**
   * Theorem --- the empty relation totally orders the empty set
   */
  val emptySetTotalOrder = Lemma(
    () |- totalOrder(pair(emptySet(), emptySet()))
  ) {
    have(totalOrder(pair(emptySet(), emptySet())) <=> (partialOrder(pair(emptySet(), emptySet())) /\ total(emptySet(), emptySet()))) by Substitution.apply2(
      false,
      firstInPairReduction of (x -> emptySet(), y -> emptySet()),
      secondInPairReduction of (x -> emptySet(), y -> emptySet())
    )(totalOrder.definition of p -> pair(emptySet(), emptySet()))
    have(thesis) by Tautology.from(lastStep, emptySetPartialOrder, emptyRelationTotalOnItself)
  }

  /**
   * Well-Order --- a partial order `p = (A, <)` is said to be a well-order if
   * it is total and if every subset of `A` has a least element under `<`.
   */
  val wellOrder = DEF(p) --> {
    val A = firstInPair(p)
    val B = variable
    val `<p` = secondInPair(p)
    totalOrder(p) /\ forall(B, (subset(B, A) /\ !(B === emptySet())) ==> exists(z, in(z, B) /\ forall(x, in(x, B) ==> (in(pair(z, x), `<p`) \/ (z === x)))))
  }

  /**
   * Theorem --- the empty set is well ordered by the empty relation.
   */
  val emptySetWellOrder = Lemma(
    () |- wellOrder(pair(emptySet(), emptySet()))
  ) {
    val woDef = have(
      wellOrder(pair(emptySet(), emptySet())) <=> (totalOrder(pair(emptySet(), emptySet())) /\ forall(
        b,
        (subset(b, emptySet()) /\ !(b === emptySet())) ==> exists(z, in(z, b) /\ forall(x, in(x, b) ==> (in(pair(z, x), secondInPair(pair(emptySet(), emptySet()))) \/ (z === x))))
      ))
    ) by Substitution.apply2(false, firstInPairReduction of (x -> emptySet(), y -> emptySet()))(wellOrder.definition of p -> pair(emptySet(), emptySet()))

    have((subset(b, emptySet()) /\ !(b === emptySet())) ==> exists(z, in(z, b) /\ forall(x, in(x, b) ==> (in(pair(z, x), secondInPair(pair(emptySet(), emptySet()))) \/ (z === x))))) by Tautology.from(
      emptySetIsItsOwnOnlySubset of x -> b
    )
    thenHave(
      forall(
        b,
        (subset(b, emptySet()) /\ !(b === emptySet())) ==> exists(z, in(z, b) /\ forall(x, in(x, b) ==> (in(pair(z, x), secondInPair(pair(emptySet(), emptySet()))) \/ (z === x))))
      )
    ) by RightForall

    have(thesis) by Tautology.from(lastStep, woDef, emptySetTotalOrder)
  }

  /**
   * Useful inherited properties
   */

  /**
   * Well-orders inherit relational-transitivity from being partial orders.
   */
  val wellOrderTransitivity = Lemma(
    wellOrder(p) |- forall(w, forall(y, forall(z, (in(pair(w, y), secondInPair(p)) /\ in(pair(y, z), secondInPair(p))) ==> in(pair(w, z), secondInPair(p)))))
  ) {
    have(thesis) by Tautology.from(wellOrder.definition, totalOrder.definition, partialOrder.definition, transitive.definition of (r -> secondInPair(p), x -> firstInPair(p)))
  }

  val transitiveSet = DEF(x) --> forall(y, in(y, x) ==> subset(y, x))

  /**
   * Theorem --- the definition of a transitive set in terms of inclusion is
   * equivalent to the subset based definition.
   */
  val transitiveSetInclusionDef = Theorem(
    () |- transitiveSet(x) <=> forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))
  ) {
    // prove defs equal
    have(forall(y, in(y, x) ==> subset(y, x)) <=> forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) subproof {
      val lhs = have(forall(y, in(y, x) ==> subset(y, x)) |- forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) subproof {
        have(forall(y, in(y, x) ==> subset(y, x)) |- forall(y, in(y, x) ==> subset(y, x))) by Hypothesis
        thenHave((forall(y, in(y, x) ==> subset(y, x)), in(y, x)) |- subset(y, x)) by InstantiateForall(y)
        thenHave((forall(y, in(y, x) ==> subset(y, x)), in(y, x)) |- forall(z, in(z, y) ==> in(z, x))) by Substitution.apply2(false, subsetAxiom of (x -> y, y -> x))
        thenHave((forall(y, in(y, x) ==> subset(y, x)), in(y, x)) |- in(z, y) ==> in(z, x)) by InstantiateForall(z)
        thenHave((forall(y, in(y, x) ==> subset(y, x))) |- (in(z, y) /\ in(y, x)) ==> in(z, x)) by Restate
        thenHave((forall(y, in(y, x) ==> subset(y, x))) |- forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) by RightForall
        thenHave((forall(y, in(y, x) ==> subset(y, x))) |- forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) by RightForall
      }

      val rhs = have(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(y, in(y, x) ==> subset(y, x))) subproof {
        have(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) by Hypothesis
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) by InstantiateForall(z)
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- (in(z, y)) ==> in(z, x)) by InstantiateForall(y)
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- forall(z, in(z, y) ==> in(z, x))) by RightForall
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- subset(y, x)) by Substitution.apply2(true, subsetAxiom of (x -> y, y -> x))
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- in(y, x) ==> subset(y, x)) by Restate
        thenHave(thesis) by RightForall
      }

      have(thesis) by Tautology.from(lhs, rhs)
    }

    have(thesis) by Tautology.from(lastStep, transitiveSet.definition)
  }

  val inclusionOnTransitiveSetIsPartialOrder = Theorem(
    transitiveSet(a) |- partialOrder(inclusionOrderOn(a))
  ) {

    // inclusion is a relation
    // anti reflexive
    // anti symmetric
    have(relationBetween(inclusionOn(a), a, a) /\ antiReflexive(inclusionOn(a), a) /\ antiSymmetric(inclusionOn(a), a)) by Tautology.from(
      inclusionIsRelation,
      inclusionIsAntiReflexive,
      inclusionIsAntiSymmetric
    )

    // and transitive

    sorry
  }

  /**
   * A set is an ordinal iff it is transitive ([[transitiveSet]]) and
   * well-ordered ([[wellOrder]]) by inclusion.
   *
   * Since inclusion is not precisely a relation in the sense of set theory, the
   * well-ordered clause is explicitly written.
   */
  val ordinal = DEF(a) --> transitiveSet(a) /\ wellOrder(inclusionOrderOn(a))

  /**
   * Defining properties of the [[ordinal]] class
   *
   *   - the [[emptySet]] is an ordinal --- [[emptySetOrdinal]]
   *   - if `a` is an ordinal and `b ∈ a`, then `b` is an ordinal --- [[ordinalInclusionClosure]]
   *   - if `a`, `b` are ordinals and `b ⊂ a`, then `b ∈ a` --- [[ordinalSubsetClosure]]
   *   - if `a` and `b` are distinct ordinals, then either `a ⊂ b` or `b ⊂ a` --- [[ordinalSOMETHING]] TODO:
   *
   * Other properties
   *
   *   - the ordinals form a proper class --- [[noSetOfOrdinals]]
   *   - every subclass of the ordinals has a minimal element --- [[ordinalSubclassHasMinimalElement]]
   */

  /**
   * Theorem --- the empty set is transitive.
   */
  val emptySetTransitive = Lemma(
    () |- transitiveSet(emptySet())
  ) {
    val hypo = have(!in(y, emptySet()) |- in(y, emptySet()) ==> subset(y, emptySet())) by Restate
    have(() |- in(y, emptySet()) ==> subset(y, emptySet())) by Cut(emptySetAxiom of (x -> y), hypo)
    thenHave(() |- forall(y, in(y, emptySet()) ==> subset(y, emptySet()))) by RightForall
    andThen(Simplify.once(true, transitiveSet.definition of (x -> emptySet())))
  }

  /**
   * Theorem --- the empty set is well ordered by inclusion.
   */
  val emptySetWellOrderedByInclusion = Lemma(
    () |- wellOrder(inclusionOrderOn(emptySet()))
  ) {
    val incDef = have(inclusionOrderOn(emptySet()) === pair(emptySet(), inclusionOn(emptySet()))) by InstantiateForall(inclusionOrderOn(emptySet()))(inclusionOrderOn.definition of a -> emptySet())
    have(wellOrder(pair(emptySet(), inclusionOn(emptySet())))) by Substitution.apply2(true, emptySetInclusionEmpty)(emptySetWellOrder)
    thenHave(thesis) by Substitution.apply2(true, incDef)
  }

  /**
   * Theorem --- the empty set is an ordinal (zero).
   */
  val emptySetOrdinal = Theorem(
    () |- ordinal(emptySet())
  ) {
    have(thesis) by Tautology.from(emptySetWellOrderedByInclusion, emptySetTransitive, ordinal.definition of (a -> emptySet()))
  }

  val ordinalsHereditarilyTransitive = Lemma(
    ordinal(a) |- transitiveSet(a) /\ forall(b, in(b, a) ==> transitiveSet(b))
  ) {
    val ordinalTrans = have(ordinal(a) |- transitiveSet(a)) by Weakening(ordinal.definition)
    val wellOrdInca = have(ordinal(a) |- wellOrder(inclusionOrderOn(a))) by Weakening(ordinal.definition)
    have(inclusionOrderOn(a) === pair(a, inclusionOn(a))) by InstantiateForall(inclusionOrderOn(a))(inclusionOrderOn.definition)
    val wellOrda = have(ordinal(a) |- wellOrder(pair(a, inclusionOn(a)))) by Substitution.apply2(false, lastStep)(wellOrdInca)

    have(transitiveSet(a) |- forall(b, in(b, a) ==> subset(b, a))) by Weakening(transitiveSet.definition of x -> a)
    val bIna = thenHave((transitiveSet(a), in(b, a)) |- subset(b, a)) by InstantiateForall(b)
    have((transitiveSet(a), in(b, a)) |- forall(z, in(z, b) ==> in(z, a))) by Tautology.from(lastStep, subsetAxiom of (x -> b, y -> a))
    thenHave((transitiveSet(a), in(b, a)) |- in(z, b) ==> in(z, a)) by InstantiateForall(z)
    val bcz = have((transitiveSet(a), in(b, a), in(z, b), in(c, z)) |- in(b, a) /\ in(c, a) /\ in(z, a)) by Tautology.from(lastStep, lastStep of (z -> c, b -> z))

    val cInb = have((in(b, a), in(z, b), in(c, z), in(c, a), in(z, a), wellOrder(pair(a, inclusionOn(a)))) |- in(c, b)) subproof {
      val bz = have(in(b, a) /\ in(z, a) /\ in(z, b) |- in(pair(z, b), inclusionOn(a))) by Weakening(inclusionOrderElem of (b -> z, c -> b))
      val zc = have(in(z, a) /\ in(c, a) /\ in(c, z) |- in(pair(c, z), inclusionOn(a))) by Weakening(inclusionOrderElem of (c -> z, b -> c))
      val bc = have(in(pair(c, b), inclusionOn(a)) |- in(b, a) /\ in(c, a) /\ in(c, b)) by Weakening(inclusionOrderElem of (c -> b, b -> c))

      have(wellOrder(pair(a, inclusionOn(a))) |- forall(w, forall(y, forall(z, (in(pair(w, y), inclusionOn(a)) /\ in(pair(y, z), inclusionOn(a))) ==> in(pair(w, z), inclusionOn(a)))))) by Substitution
        .apply2(false, secondInPairReduction of (x -> a, y -> inclusionOn(a)))(wellOrderTransitivity of p -> pair(a, inclusionOn(a)))
      thenHave(wellOrder(pair(a, inclusionOn(a))) |- forall(y, forall(z, (in(pair(c, y), inclusionOn(a)) /\ in(pair(y, z), inclusionOn(a))) ==> in(pair(c, z), inclusionOn(a))))) by InstantiateForall(
        c
      )
      thenHave(wellOrder(pair(a, inclusionOn(a))) |- forall(w, (in(pair(c, z), inclusionOn(a)) /\ in(pair(z, w), inclusionOn(a))) ==> in(pair(c, w), inclusionOn(a)))) by InstantiateForall(z)
      thenHave(wellOrder(pair(a, inclusionOn(a))) |- (in(pair(c, z), inclusionOn(a)) /\ in(pair(z, b), inclusionOn(a))) ==> in(pair(c, b), inclusionOn(a))) by InstantiateForall(b)

      have(thesis) by Tautology.from(lastStep, bz, zc, bc)
    }

    have((transitiveSet(a), wellOrder(pair(a, inclusionOn(a))), in(b, a), in(z, b), in(c, z)) |- in(c, b)) by Tautology.from(bcz, cInb)
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a))), in(b, a)) |- (in(c, z) /\ in(z, b)) ==> in(c, b)) by Restate
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a))), in(b, a)) |- forall(z, (in(c, z) /\ in(z, b)) ==> in(c, b))) by RightForall
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a))), in(b, a)) |- forall(c, forall(z, (in(c, z) /\ in(z, b)) ==> in(c, b)))) by RightForall
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a))), in(b, a)) |- transitiveSet(b)) by Substitution.apply2(true, transitiveSetInclusionDef of x -> b)
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a)))) |- in(b, a) ==> transitiveSet(b)) by Restate
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a)))) |- forall(b, in(b, a) ==> transitiveSet(b))) by RightForall

    have(thesis) by Tautology.from(lastStep, wellOrda, ordinalTrans)
  }

  val elementsOfOrdinalsAreOrdinals = Theorem(
    (ordinal(a), in(b, a)) |- ordinal(b)
  ) {
    assume(ordinal(a))
    assume(in(b, a))

    // transitive ::
    val transitiveB = have(transitiveSet(b)) subproof {
      have(forall(b, in(b, a) ==> transitiveSet(b))) by Weakening(ordinalsHereditarilyTransitive)
      thenHave(thesis) by InstantiateForall(b)
    }

    // and well ordered by inclusion ::

    // what defines \in_b as a subset of \in_a?
    // one direction (a ==> b) is sufficient here
    val incAToB = have(in(y, b) /\ in(z, b) /\ in(pair(z, y), inclusionOn(a)) |- in(pair(z, y), inclusionOn(b))) subproof {
      assume(in(y, b))
      assume(in(z, b))
      assume(in(pair(z, y), inclusionOn(a)))

      // instantiating definition of inclusion (a bit painful with assumes)
      have(forall(z, (z === inclusionOn(a)) <=> forall(t, in(t, z) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))))) by Weakening(inclusionOn.definition)
      thenHave(forall(t, in(t, inclusionOn(a)) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(inclusionOn(a))
      val incDefA =
        thenHave(in(pair(z, y), inclusionOn(a)) <=> (in(pair(z, y), cartesianProduct(a, a)) /\ exists(d, exists(c, in(d, c) /\ (pair(z, y) === pair(d, c)))))) by InstantiateForall(pair(z, y))
      have(forall(z, (z === inclusionOn(b)) <=> forall(t, in(t, z) <=> (in(t, cartesianProduct(b, b)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))))) by Weakening(
        inclusionOn.definition of a -> b
      )
      thenHave(forall(t, in(t, inclusionOn(b)) <=> (in(t, cartesianProduct(b, b)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(inclusionOn(b))
      val incDefB =
        thenHave(in(pair(z, y), inclusionOn(b)) <=> (in(pair(z, y), cartesianProduct(b, b)) /\ exists(d, exists(c, in(d, c) /\ (pair(z, y) === pair(d, c)))))) by InstantiateForall(pair(z, y))

      have(in(pair(z, y), cartesianProduct(b, b))) by Tautology.from(pairInCartesianProduct of (a -> z, b -> y, x -> b, y -> b))
      have(thesis) by Tautology.from(lastStep, incDefA, incDefB)
    }

    val totalB = have(totalOrder(inclusionOrderOn(b))) subproof {
      // the totality of \in_b follows from the totality of \in_a and the fact that \in_b does not exclude any elements of b
      val totA = have(totalOrder(inclusionOrderOn(a))) by Tautology.from(ordinal.definition, wellOrder.definition of p -> inclusionOrderOn(a))

      val totalDef = have(totalOrder(p) <=> (partialOrder(p) /\ total(secondInPair(p), firstInPair(p)))) by Weakening(totalOrder.definition)

      // \in_b is a partial order
      val inBPartial = have(partialOrder(inclusionOrderOn(b))) by Tautology.from(inclusionOnTransitiveSetIsPartialOrder of a -> b, transitiveB)

      // \in_b is total as a homogeneous relation on b
      val inBTotal = have(total(secondInPair(inclusionOrderOn(b)), firstInPair(inclusionOrderOn(b)))) subproof {
        val totB = have(total(inclusionOn(b), b)) subproof {
          have(forall(z, (z === inclusionOrderOn(a)) <=> (z === pair(a, inclusionOn(a))))) by Weakening(inclusionOrderOn.definition)
          val incEq = thenHave(inclusionOrderOn(a) === pair(a, inclusionOn(a))) by InstantiateForall(inclusionOrderOn(a))
          have(total(secondInPair(inclusionOrderOn(a)), firstInPair(inclusionOrderOn(a)))) by Tautology.from(totalDef of p -> inclusionOrderOn(a), totA)
          thenHave(total(secondInPair(pair(a, inclusionOn(a))), firstInPair(pair(a, inclusionOn(a))))) by Substitution.apply2(false, incEq)
          val totIncA = thenHave(total(inclusionOn(a), a)) by Substitution.apply2(false, secondInPairReduction of (x -> a, y -> inclusionOn(a)), firstInPairReduction of (x -> a, y -> inclusionOn(a)))

          val totRelDef =
            have(total(r, x) <=> (relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z)))))) by Weakening(total.definition)

          // need to show
          // \forall y, z \in b. y \in_b z \/ z \in_b y \/ (z = y)
          // y, z \in b ==> y, z \in a
          // y, z \in a ==> y \in_a z \/ z \in_a y \/ (z = y)
          // but each of these imply a literal above
          // done
          have(total(inclusionOn(a), a) |- (in(y, b) /\ in(z, b)) ==> (in(pair(y, z), inclusionOn(b)) \/ in(pair(z, y), inclusionOn(b)) \/ (y === z))) subproof {
            assume(total(inclusionOn(a), a))
            assume(in(y, b))
            assume(in(z, b))

            have(forall(y, in(y, a) ==> subset(y, a))) by Tautology.from(ordinal.definition, transitiveSet.definition of x -> a)
            thenHave(in(b, a) ==> subset(b, a)) by InstantiateForall(b)
            have(forall(x, in(x, b) ==> in(x, a))) by Tautology.from(lastStep, subsetAxiom of (x -> b, y -> a))
            thenHave(in(x, b) ==> in(x, a)) by InstantiateForall(x)
            val yza = have(in(y, a) /\ in(z, a)) by Tautology.from(lastStep of x -> y, lastStep of x -> z)

            have(forall(y, forall(z, (in(y, a) /\ in(z, a)) ==> (in(pair(y, z), inclusionOn(a)) \/ in(pair(z, y), inclusionOn(a)) \/ (y === z))))) by Tautology.from(
              totRelDef of (r -> inclusionOn(a), x -> a)
            )
            thenHave((in(y, a) /\ in(z, a)) ==> (in(pair(y, z), inclusionOn(a)) \/ in(pair(z, y), inclusionOn(a)) \/ (y === z))) by InstantiateForall(y, z)
            have((in(pair(y, z), inclusionOn(a)) \/ in(pair(z, y), inclusionOn(a)) \/ (y === z))) by Tautology.from(lastStep, yza)

            have(thesis) by Tautology.from(lastStep, incAToB, incAToB of (y -> z, z -> y))
          }

          have((in(y, b) /\ in(z, b)) ==> (in(pair(y, z), inclusionOn(b)) \/ in(pair(z, y), inclusionOn(b)) \/ (y === z))) by Cut(totIncA, lastStep)
          thenHave(forall(z, (in(y, b) /\ in(z, b)) ==> (in(pair(y, z), inclusionOn(b)) \/ in(pair(z, y), inclusionOn(b)) \/ (y === z)))) by RightForall
          thenHave(forall(y, forall(z, (in(y, b) /\ in(z, b)) ==> (in(pair(y, z), inclusionOn(b)) \/ in(pair(z, y), inclusionOn(b)) \/ (y === z))))) by RightForall

          have(thesis) by Tautology.from(lastStep, inclusionIsRelation of a -> b, totRelDef of (r -> inclusionOn(b), x -> b))
        }

        have(forall(z, (z === inclusionOrderOn(b)) <=> (z === pair(b, inclusionOn(b))))) by Weakening(inclusionOrderOn.definition of a -> b)
        val incEq = thenHave(inclusionOrderOn(b) === pair(b, inclusionOn(b))) by InstantiateForall(inclusionOrderOn(b))

        have(secondInPair(pair(b, inclusionOn(b))) === inclusionOn(b)) by Weakening(secondInPairReduction of (x -> b, y -> inclusionOn(b)))
        val snd = thenHave(secondInPair(inclusionOrderOn(b)) === inclusionOn(b)) by Substitution.apply2(true, incEq)
        have(firstInPair(pair(b, inclusionOn(b))) === (b)) by Weakening(firstInPairReduction of (x -> b, y -> inclusionOn(b)))
        val fst = thenHave(firstInPair(inclusionOrderOn(b)) === (b)) by Substitution.apply2(true, incEq)

        have(thesis) by Substitution.apply2(true, snd, fst)(totB)
      }

      have(totalOrder(inclusionOrderOn(b)) <=> (partialOrder(inclusionOrderOn(b)) /\ total(secondInPair(inclusionOrderOn(b)), firstInPair(inclusionOrderOn(b))))) by Weakening(
        totalDef of p -> inclusionOrderOn(b)
      )
      have(thesis) by Tautology.from(lastStep, inBPartial, inBTotal)
    }

    val woProp = have(forall(c, (subset(c, b) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(b)) \/ (z === y)))))) subproof {
      // painful expansion
      // subset c b ==> subset c a
      have(forall(y, in(y, a) ==> subset(y, a))) by Tautology.from(ordinal.definition, transitiveSet.definition of x -> a)
      thenHave(in(b, a) ==> subset(b, a)) by InstantiateForall(b)
      thenHave(subset(b, a)) by Restate
      have(subset(c, b) |- subset(c, a)) by Tautology.from(lastStep, subsetTransitivity of (a -> c, c -> a))
      val bToA = thenHave(subset(c, b) /\ !(c === emptySet()) |- subset(c, a) /\ !(c === emptySet())) by Tautology

      have(forall(z, (z === inclusionOrderOn(a)) <=> (z === pair(a, inclusionOn(a))))) by Weakening(inclusionOrderOn.definition)
      val incDef = thenHave(inclusionOrderOn(a) === pair(a, inclusionOn(a))) by InstantiateForall(inclusionOrderOn(a))

      // so there exists a minimal element wrt a
      have(
        forall(
          c,
          (subset(c, firstInPair(inclusionOrderOn(a))) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), secondInPair(inclusionOrderOn(a))) \/ (z === y))))
        )
      ) by Tautology.from(ordinal.definition, wellOrder.definition of p -> inclusionOrderOn(a))
      thenHave(
        forall(
          c,
          (subset(c, firstInPair(pair(a, inclusionOn(a)))) /\ !(c === emptySet())) ==> exists(
            z,
            in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), secondInPair(pair(a, inclusionOn(a)))) \/ (z === y)))
          )
        )
      ) by Substitution.apply2(false, incDef)
      thenHave(forall(c, (subset(c, a) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y)))))) by Substitution.apply2(
        false,
        firstInPairReduction of (x -> a, y -> inclusionOn(a)),
        secondInPairReduction of (x -> a, y -> inclusionOn(a))
      )
      val caWO = thenHave((subset(c, a) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))))) by InstantiateForall(c)

      // but if this element is minimal wrt \in_a, it is minimal wrt \in_b as well
      have(
        (subset(c, b), exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))))) |- exists(
          z,
          in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(b)) \/ (z === y)))
        )
      ) subproof {
        assume(subset(c, b))
        val subCB = have(forall(x, in(x, c) ==> in(x, b))) by Tautology.from(subsetAxiom of (x -> c, y -> b))
        val yb = have(in(y, c) ==> in(y, b)) by InstantiateForall(y)(subCB)
        val zb = have(in(z, c) ==> in(z, b)) by InstantiateForall(z)(subCB)

        have(in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))) |- forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y)))) by Restate
        thenHave(in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))) |- in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))) by InstantiateForall(y)
        have(in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))) |- in(y, c) ==> (in(pair(z, y), inclusionOn(b)) \/ (z === y))) by Tautology.from(
          lastStep,
          incAToB,
          yb,
          zb
        )
        thenHave(in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))) |- forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(b)) \/ (z === y)))) by RightForall
        thenHave(in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))) |- in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(b)) \/ (z === y)))) by Tautology
        thenHave(
          in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y))) |- exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(b)) \/ (z === y))))
        ) by RightExists
        thenHave(thesis) by LeftExists
      }

      have((subset(c, b) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(b)) \/ (z === y))))) by Tautology.from(lastStep, caWO, bToA)
      thenHave(thesis) by RightForall
    }

    val wo = have(wellOrder(inclusionOrderOn(b))) subproof {
      have(forall(z, (z === inclusionOrderOn(b)) <=> (z === pair(b, inclusionOn(b))))) by Weakening(inclusionOrderOn.definition of a -> b)
      val incDef = thenHave(inclusionOrderOn(b) === pair(b, inclusionOn(b))) by InstantiateForall(inclusionOrderOn(b))

      have(
        forall(
          c,
          (subset(c, firstInPair(pair(b, inclusionOn(b)))) /\ !(c === emptySet())) ==> exists(
            z,
            in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), secondInPair(pair(b, inclusionOn(b)))) \/ (z === y)))
          )
        )
      ) by Substitution.apply2(true, firstInPairReduction of (x -> b, y -> inclusionOn(b)), secondInPairReduction of (x -> b, y -> inclusionOn(b)))(woProp)
      thenHave(
        forall(
          c,
          (subset(c, firstInPair(inclusionOrderOn(b))) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), secondInPair(inclusionOrderOn(b))) \/ (z === y))))
        )
      ) by Substitution.apply2(true, incDef)
      have(thesis) by Tautology.from(lastStep, totalB, wellOrder.definition of p -> inclusionOrderOn(b))
    }

    have(thesis) by Tautology.from(wo, transitiveB, ordinal.definition of (a -> b))
  }

  val ordinalSubclassHasMinimalElement = Lemma(
    forall(x, P(x) ==> ordinal(x)) /\ exists(x, P(x)) |- exists(y, P(y) /\ ordinal(y) /\ forall(x, P(x) ==> in(y, x)))
  ) {
    sorry
  }

  /**
   * Transfinite Recursion
   */

  val initialSegmentUniqueness = Lemma(
    existsOne(z, forall(t, in(t, z) <=> (in(t, firstInPair(p)) /\ in(pair(t, a), secondInPair(p)))))
  ) {
    have(thesis) by UniqueComprehension(firstInPair(p), lambda(Seq(t, z), in(pair(t, a), secondInPair(p))))
  }

  val initialSegment = DEF(p, a) --> The(z, forall(t, in(t, z) <=> (in(t, firstInPair(p)) /\ in(pair(t, a), secondInPair(p)))))(initialSegmentUniqueness)

  val initialSegmentLeqUniqueness = Lemma(
    existsOne(z, forall(t, in(t, z) <=> (in(t, firstInPair(p)) /\ (in(pair(t, a), secondInPair(p)) \/ (t === a)))))
  ) {
    have(thesis) by UniqueComprehension(firstInPair(p), lambda(Seq(t, z), (in(pair(t, a), secondInPair(p)) \/ (t === a))))
  }

  val initialSegmentLeq = DEF(p, a) --> The(z, forall(t, in(t, z) <=> (in(t, firstInPair(p)) /\ (in(pair(t, a), secondInPair(p)) \/ (t === a)))))(initialSegmentLeqUniqueness)

  val initialSegmentOrderUniqueness = Lemma(
    existsOne(z, forall(t, in(t, z) <=> (in(t, secondInPair(p)) /\ (in(firstInPair(t), initialSegment(p, a)) /\ in(secondInPair(t), initialSegment(p, a))))))
  ) {
    have(thesis) by UniqueComprehension(secondInPair(p), lambda(Seq(t, z), (in(firstInPair(t), initialSegment(p, a)) /\ in(secondInPair(t), initialSegment(p, a)))))
  }
  val initialSegmentOrder =
    DEF(p, a) --> The(z, forall(t, in(t, z) <=> (in(t, secondInPair(p)) /\ (in(firstInPair(t), initialSegment(p, a)) /\ in(secondInPair(t), initialSegment(p, a))))))(initialSegmentOrderUniqueness)

  val initialSegmentsSubset = Lemma(
    partialOrder(p) /\ in(pair(x, y), secondInPair(p)) |- subset(initialSegment(p, x), initialSegment(p, y))
  ) {
    // t \in <x iff t \in p1 and (t, x) \in p2

    // but we know (x, y) \in p2, so by transitivity, (t, y) \in p2

    // t \in p1 /\ (t, y) in p2 ==> t \in <y

    // <x \subseteq <y

    sorry
  }

  val initialSegmentLeqBreakdown = Lemma(
    in(t, initialSegmentLeq(p, a)) <=> (in(t, initialSegment(p, a)) \/ (t === a))
  ) {
    sorry
  }

  val initialSegmentOrderTotal = Lemma(
    totalOrder(p) /\ in(a, firstInPair(p)) |- total(initialSegmentOrder(p, a), initialSegment(p, a))
  ) {
    sorry
  }

  // initial segment of well order is well ordered under the restricted order
  val initialSegmentWellOrdered = Lemma(
    wellOrder(p) /\ in(a, firstInPair(p)) |- wellOrder(pair(initialSegment(p, a), initialSegmentOrder(p, a)))
  ) {

    sorry
  }

  /**
   * The restriction of a function `f` with respect to `a` relative to a
   * partial order `p = (X, <)`. The result is `f` with its domain restricted
   * to the elements less than `a` wrt `<`.
   */
  val orderedRestriction = DEF(f, a, p) --> restrictedFunction(f, initialSegment(p, a))

  val orderedRestrictionFunctionalOverInit = Lemma(
    functionalOver(orderedRestriction(f, a, p), initialSegment(p, a))
  ) {
    sorry
  }

  /**
   * Theorem --- Well Ordered Induction on a Subclass
   *
   * If `p` is a strict well-ordering, and `Q` is a subclass of the base set of
   * `p`, called `A`, then
   *
   *     `\forall x \in A. (A |^ x) \subseteq Q ==> x \in Q |- A = Q`
   *
   * i.e., if `Q` is a subclass of `A`, and the property `Q` passes to `x` from
   * its initial segment, then `A` is `Q`.
   */
  val wellOrderedInductionSubclass = Theorem(
    {
      val A = firstInPair(p)
      (
        wellOrder(p),
        forall(x, Q(x) ==> in(x, A)),
        forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
      )
        |- forall(x, Q(x) <=> in(x, A))
    }
  ) {
    // renaming
    val A = firstInPair(p)
    val `<p` = secondInPair(p)

    // proof assumptions
    assume(
      Seq(
        wellOrder(p),
        forall(x, Q(x) ==> in(x, A)),
        forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
      )
    )

    // assume, towards a contradiction
    val contra = !forall(x, Q(x) <=> in(x, A))
    assume(contra)

    val contraDis = have(exists(x, (Q(x) /\ !in(x, A)) \/ (!Q(x) /\ in(x, A)))) by Restate

    val lhs = have(Q(x) /\ !in(x, A) |- ()) subproof {
      have(Q(x) ==> in(x, A)) by InstantiateForall
      thenHave(thesis) by Tautology
    }

    val rhs = have(!Q(x) /\ in(x, A) |- ()) subproof {
      val zDef = forall(t, in(t, z) <=> (in(t, A) /\ !Q(t)))

      // z exists by comprehension
      val zExists = have(exists(z, zDef)) subproof {
        have(existsOne(z, zDef)) by UniqueComprehension(A, lambda(Seq(t, x), !Q(t)))
        have(thesis) by Cut(lastStep, existsOneImpliesExists of P -> lambda(z, zDef))
      }

      // z is a subset of A
      val zSubset = have(zDef |- subset(z, A)) subproof {
        have(zDef |- in(t, z) <=> (in(t, A) /\ !Q(t))) by InstantiateForall
        thenHave(zDef |- in(t, z) ==> in(t, A)) by Weakening
        thenHave(zDef |- forall(t, in(t, z) ==> in(t, A))) by RightForall
        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> z, y -> A))
      }

      // there exists a least element y in z
      val yDef = in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))
      val yExists = have((zDef, !Q(x) /\ in(x, A)) |- exists(y, yDef)) subproof {
        assume(Seq(zDef, !Q(x) /\ in(x, A)))
        have(in(x, z) <=> (in(x, A) /\ !Q(x))) by InstantiateForall
        thenHave(in(x, z)) by Tautology
        val zNonEmpty = have(!(z === emptySet())) by Tautology.from(lastStep, setWithElementNonEmpty of (y -> x, x -> z))

        have(forall(b, (subset(b, A) /\ !(b === emptySet())) ==> exists(y, in(y, b) /\ forall(w, in(w, b) ==> (in(pair(y, w), `<p`) \/ (y === w)))))) by Tautology.from(wellOrder.definition)
        thenHave((subset(z, A) /\ !(z === emptySet())) ==> exists(y, in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))))) by InstantiateForall(z)

        val exY = have(exists(y, in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))))) by Tautology.from(lastStep, zNonEmpty, zSubset)

        // tiny proof inside quantifiers
        have(in(w, z) <=> (in(w, A) /\ !Q(w))) by InstantiateForall
        thenHave(in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w)) |- (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))) by Tautology
        thenHave(forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))) by LeftForall
        thenHave(forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))) by RightForall
        thenHave(in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))) by Tautology
        thenHave(
          in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- exists(y, in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))))
        ) by RightExists
        thenHave(
          exists(y, in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w)))) |- exists(y, in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))))
        ) by LeftExists

        have(exists(y, in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))))) by Tautology.from(lastStep, exY)
      }

      // elements of the initial segment of A wrt y satisfy Q
      val yInitInQ = have((zDef, yDef) |- forall(w, in(w, initialSegment(p, y)) ==> Q(w))) subproof {
        assume(Seq(zDef, yDef))

        // TODO: assumptions annoy instantiations of external imports, so this is done rather verbosely here
        // see https://github.com/epfl-lara/lisa/issues/161
        have(forall(z, (z === initialSegment(p, y)) <=> forall(t, in(t, z) <=> (in(t, A) /\ in(pair(t, y), `<p`))))) by Weakening(initialSegment.definition of (a -> y))
        thenHave(forall(t, in(t, initialSegment(p, y)) <=> (in(t, A) /\ in(pair(t, y), `<p`)))) by InstantiateForall(initialSegment(p, y))
        val wInInit = thenHave((in(w, initialSegment(p, y)) <=> (in(w, A) /\ in(pair(w, y), `<p`)))) by InstantiateForall(w)

        have((in(w, A) /\ in(pair(w, y), `<p`)) |- Q(w)) subproof {
          assume(Seq((in(w, A) /\ in(pair(w, y), `<p`)), !Q(w)))

          have(forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))) by Restate
          thenHave((!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))) by InstantiateForall(w)
          val cases = thenHave((in(pair(y, w), `<p`) \/ (y === w))) by Tautology

          val rhs = have(!(y === w)) subproof {
            // well order is anti reflexive
            assume(y === w)
            have(in(pair(w, y), `<p`)) by Restate
            val ww = thenHave(in(pair(w, w), `<p`)) by Substitution.apply2(false, y === w)

            have(∀(y, in(y, A) ==> !in(pair(y, y), `<p`))) subproof {
              have(antiReflexive(`<p`, A)) by Tautology.from(wellOrder.definition, totalOrder.definition, partialOrder.definition)
              have(thesis) by Tautology.from(lastStep, antiReflexive.definition of (r -> `<p`, x -> A))
            }

            thenHave(in(w, A) ==> !in(pair(w, w), `<p`)) by InstantiateForall(w)
            have(thesis) by Tautology.from(lastStep, ww)
          }

          val lhs = have(!in(pair(y, w), `<p`)) subproof {
            // well order is anti-symmetric
            assume(in(pair(y, w), `<p`))
            val yw = have(in(pair(y, w), `<p`) /\ in(pair(w, y), `<p`)) by Restate

            have(∀(y, ∀(w, (in(pair(y, w), `<p`) /\ in(pair(w, y), `<p`)) ==> (y === w)))) subproof {
              have(antiSymmetric(`<p`, A)) by Tautology.from(wellOrder.definition, totalOrder.definition, partialOrder.definition)
              have(thesis) by Tautology.from(lastStep, antiSymmetric.definition of (r -> `<p`, x -> A))
            }

            thenHave((in(pair(y, w), `<p`) /\ in(pair(w, y), `<p`)) ==> (y === w)) by InstantiateForall(y, w)
            have(thesis) by Tautology.from(lastStep, yw, rhs)
          }

          have(thesis) by Tautology.from(lhs, rhs, cases)
        }

        have(in(w, initialSegment(p, y)) ==> Q(w)) by Tautology.from(lastStep, wInInit)
        thenHave(thesis) by RightForall
      }

      // but if the initial segment of y is a subset of Q, then y is in Q
      val yInQ = have((zDef, yDef, in(y, A)) |- Q(y)) subproof {
        have(in(y, A) ==> (forall(w, in(w, initialSegment(p, y)) ==> Q(w)) ==> Q(y))) by InstantiateForall
        thenHave((in(y, A), (forall(w, in(w, initialSegment(p, y)) ==> Q(w)))) |- Q(y)) by Restate
        have(thesis) by Cut(yInitInQ, lastStep)
      }

      // however, we know y is in z, so !Q(y), hence contradiction
      have((zDef, yDef) |- ()) subproof {
        assume(Seq(zDef, yDef))
        val ynotQ = have(in(y, z) <=> (in(y, A) /\ !Q(y))) by InstantiateForall
        have(in(y, z)) by Restate
        have(thesis) by Tautology.from(lastStep, ynotQ, yInQ)
      }

      thenHave((zDef, exists(y, yDef)) |- ()) by LeftExists
      have((zDef, !Q(x) /\ in(x, A)) |- ()) by Cut(yExists, lastStep)
      thenHave((exists(z, zDef), !Q(x) /\ in(x, A)) |- ()) by LeftExists
      have(thesis) by Cut(zExists, lastStep)
    }

    have(((Q(x) /\ !in(x, A)) \/ (!Q(x) /\ in(x, A))) |- ()) by Tautology.from(lhs, rhs)
    thenHave(exists(x, (Q(x) /\ !in(x, A)) \/ (!Q(x) /\ in(x, A))) |- ()) by LeftExists

    have(thesis) by Tautology.from(lastStep, contraDis)
  }

  /**
   * Theorem --- Well Ordered Induction
   *
   * If `p` is a strict well-ordering, `Q` is a class, and `A` the base set of
   * `p`, then
   *
   *     `∀ x ∈ A. (A |^ x) ⊆ Q ==> x ∈ Q |- ∀ x ∈ A. x ∈ Q`
   *
   * i.e., if the property `Q` passes to `x` from its initial segment, then `Q`
   * holds for every element of `A`.
   */
  val wellOrderedInduction = Theorem(
    {
      val A = firstInPair(p)
      (
        wellOrder(p),
        forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
      )
        |- forall(x, in(x, A) ==> Q(x))
    }
  ) {
    val A = firstInPair(p)
    val `<p` = secondInPair(p)

    assume(
      Seq(
        wellOrder(p),
        forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
      )
    )

    // make a subclass out of Q by intersecting with A
    def prop(x: Term): Formula = Q(x) /\ in(x, A)

    have(prop(x) ==> in(x, A)) by Restate
    val subclassProp = thenHave(forall(x, prop(x) ==> in(x, A))) by Restate

    have(forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x)))) subproof {
      have(in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x))) by InstantiateForall
      val fy = thenHave(in(x, A) |- (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x))) by Restate
      // have(forall(y, in(y, initialSegment(p, x)) ==> Q(y)) |- (in(y, initialSegment(p, x)) ==> Q(y))) by InstantiateForall
      // val inst = have(in(x, A) |- (in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)) by Tautology.from(lastStep, fy)

      have(in(y, initialSegment(p, x)) |- in(y, A)) subproof {
        have(forall(z, (z === initialSegment(p, x)) <=> forall(t, in(t, z) <=> (in(t, A) /\ in(pair(t, x), `<p`))))) by Weakening(initialSegment.definition of (a -> x))
        thenHave(forall(t, in(t, initialSegment(p, x)) <=> (in(t, A) /\ in(pair(t, x), `<p`)))) by InstantiateForall(initialSegment(p, x))
        thenHave((in(y, initialSegment(p, x)) <=> (in(y, A) /\ in(pair(y, x), `<p`)))) by InstantiateForall(y)
        thenHave(thesis) by Tautology
      }

      have((in(y, initialSegment(p, x)) ==> Q(y)) <=> (in(y, initialSegment(p, x)) ==> prop(y))) by Tautology.from(lastStep)
      thenHave(forall(y, (in(y, initialSegment(p, x)) ==> Q(y)) <=> (in(y, initialSegment(p, x)) ==> prop(y)))) by RightForall
      have(forall(y, in(y, initialSegment(p, x)) ==> Q(y)) <=> forall(y, in(y, initialSegment(p, x)) ==> prop(y))) by Cut(
        lastStep,
        universalEquivalenceDistribution of (P -> lambda(y, in(y, initialSegment(p, x)) ==> Q(y)), Q -> lambda(y, in(y, initialSegment(p, x)) ==> prop(y)))
      )

      have(in(x, A) |- forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x)) by Tautology.from(lastStep, fy)
      thenHave(in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x))) by Restate
      thenHave(thesis) by RightForall
    }

    have(forall(x, in(x, A) <=> prop(x))) by Tautology.from(lastStep, subclassProp, wellOrderedInductionSubclass of Q -> lambda(x, prop(x)))
    thenHave(in(x, A) <=> prop(x)) by InstantiateForall(x)
    thenHave(in(x, A) ==> Q(x)) by Tautology
    thenHave(thesis) by RightForall
  }

  val transfiniteInduction = Theorem(
    forall(x, ordinal(x) ==> (forall(y, in(y, x) ==> Q(y)) ==> Q(x))) |- forall(x, ordinal(x) ==> Q(x))
  ) {

    assume(forall(x, ordinal(x) ==> (forall(y, in(y, x) ==> Q(y)) ==> Q(x))))
    assume(exists(x, ordinal(x) /\ !Q(x))) // negated conclusion

    // we assume the negated conjecture and derive a contradiction

    // prop := On \ Q
    def prop(x: Term) = ordinal(x) /\ !Q(x)

    // there is a minimal element in prop
    val yDef = prop(y) /\ forall(x, prop(x) ==> in(y, x))

    have(prop(x) ==> ordinal(x)) by Restate
    thenHave(forall(x, prop(x) ==> ordinal(x)))
    val yExists = have(exists(y, yDef)) by Tautology.from(lastStep, ordinalSubclassHasMinimalElement of (P -> lambda(x, prop(x))))

    // so everything less than y is not in prop
    val fz = have(yDef |- forall(z, in(z, y) ==> !prop(z))) subproof {
      assume(yDef)

      // assume z \in y
      // but \forall x. prop(x) ==> y \in x
      // so prop(z) ==> y \in z
      have(forall(x, prop(x) ==> in(y, x))) by Restate
      thenHave(prop(z) ==> in(y, z)) by InstantiateForall(z)

      // but inclusion is anti symmetric (regularity)
      have(in(z, y) |- !prop(z)) by Tautology.from(lastStep, inclusionAntiSymmetric of (x -> z, y -> y))
      thenHave(in(z, y) ==> !prop(z)) by Restate
      thenHave(thesis) by RightForall
    }

    // but by assumption, this must mean Q(y)
    have(yDef |- Q(y)) subproof {
      assume(yDef)
      have(forall(z, in(z, y) ==> !prop(z))) by Restate.from(fz)
      thenHave(in(z, y) ==> !prop(z)) by InstantiateForall(z)
      have(in(z, y) ==> Q(z)) by Tautology.from(lastStep, elementsOfOrdinalsAreOrdinals of (b -> z, a -> y))
      val zy = thenHave(forall(z, in(z, y) ==> Q(z))) by RightForall
      have(ordinal(y) ==> (forall(z, in(z, y) ==> Q(z)) ==> Q(y))) by InstantiateForall
      have(thesis) by Tautology.from(zy, lastStep)
    }

    // contradiction
    thenHave(yDef |- ()) by Tautology
    thenHave(exists(y, yDef) |- ()) by LeftExists
    have(() |- ()) by Cut(yExists, lastStep)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Well-Ordered Recursion (stronger version)
   */
  val wellOrderedRecursionStronger = Lemma(
    wellOrder(p) |- forall(
      t,
      in(t, firstInPair(p)) ==> existsOne(g, (functionalOver(g, initialSegment(p, t)) /\ forall(a, in(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p))))))
    )
  ) {

    assume(wellOrder(p))

    val p1 = firstInPair(p)
    val p2 = secondInPair(p)

    def fun(g: Term, t: Term): Formula = (functionalOver(g, initialSegment(p, t)) /\ forall(a, in(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p)))))
    def prop(t: Term): Formula = in(t, p1) ==> existsOne(g, fun(g, t))

    // the existence of g propagates up from initial segments
    val initPropagate = have(in(x, p1) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x))) subproof {

      assume(
        Seq(
          in(x, p1),
          forall(y, in(y, initialSegment(p, x)) ==> prop(y))
        )
      )

      // UNIQUENESS ---------------------------------------
      // if a g exists, it is unique
      val gUnique = have(exists(g, fun(g, t)) /\ in(t, p1) |- existsOne(g, fun(g, t))) subproof {
        assume(in(t, p1))

        // pt is a well order over t, which is needed for induction
        val pt = pair(initialSegment(p, t), initialSegmentOrder(p, t))
        val ptWO = have(wellOrder(pt)) by Weakening(initialSegmentWellOrdered of a -> t)

        // suppose there exist two such distinct functions g1 and g2
        val g1 = variable
        val g2 = variable

        // expansion of ordered restriction
        val ordResDef = have(orderedRestriction(g, z, p) === restrictedFunction(g, initialSegment(p, z))) subproof {
          have(forall(b, (b === orderedRestriction(g, z, p)) <=> (b === restrictedFunction(g, initialSegment(p, z))))) by Weakening(orderedRestriction.definition of (f -> g, a -> z))
          thenHave(thesis) by InstantiateForall(orderedRestriction(g, z, p))
        }

        // if g1 and g2 agree on the initial segment of an element < z, they must agree on z
        val initToz = have(
          fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) /\ in(z, initialSegment(p, t)) /\ forall(
            b,
            in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))
          ) |- (app(g1, z) === app(g2, z))
        ) subproof {
          assume(fun(g1, t))
          assume(fun(g2, t))
          assume(!(g1 === g2))
          assume(in(z, initialSegment(p, t)))
          assume(forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))))

          // the ordered restriction of g1 has domain initialSegment(p, z)
          // it is functional, too
          val restrictionIsFunction = have(fun(g, t) |- functionalOver(orderedRestriction(g, z, p), initialSegment(p, z))) subproof {
            assume(fun(g, t))

            // g_z has dom <z \cup dom g
            val domrestriction = have(functionalOver(orderedRestriction(g, z, p), setIntersection(initialSegment(p, z), relationDomain(g)))) subproof {
              have(functionalOver(restrictedFunction(g, initialSegment(p, z)), setIntersection(initialSegment(p, z), relationDomain(g)))) by Weakening(
                restrictedFunctionIsFunctionalOver of (f -> g, x -> initialSegment(p, z))
              )
              thenHave(thesis) by Substitution.apply2(true, ordResDef)
            }

            // but dom g is <t
            val domgz = have(functionalOver(orderedRestriction(g, z, p), setIntersection(initialSegment(p, z), initialSegment(p, t)))) subproof {
              have(functionalOver(g, initialSegment(p, t))) by Tautology
              have(relationDomain(g) === initialSegment(p, t)) by Tautology.from(lastStep, functionalOverImpliesDomain of (f -> g, x -> initialSegment(p, t)))

              have(thesis) by Substitution.apply2(false, lastStep)(domrestriction)
            }

            // <z \subseteq <t
            have(subset(initialSegment(p, z), initialSegment(p, t))) subproof {
              have(forall(z, (z === initialSegment(p, t)) <=> forall(b, in(b, z) <=> (in(b, p1) /\ in(pair(b, t), p2))))) by Weakening(initialSegment.definition of a -> t)
              thenHave(forall(b, in(b, initialSegment(p, t)) <=> (in(b, p1) /\ in(pair(b, t), p2)))) by InstantiateForall(initialSegment(p, t))
              thenHave(in(z, initialSegment(p, t)) <=> (in(z, p1) /\ in(pair(z, t), p2))) by InstantiateForall(z)
              val zLTt = thenHave(in(pair(z, t), p2)) by Tautology

              have(partialOrder(p)) by Tautology.from(wellOrder.definition, totalOrder.definition)

              have(thesis) by Tautology.from(lastStep, zLTt, initialSegmentsSubset of (x -> z, y -> t))
            }

            // so dom g = <z
            have(setIntersection(initialSegment(p, z), initialSegment(p, t)) === initialSegment(p, z)) by Tautology.from(
              lastStep,
              intersectionOfSubsets of (x -> initialSegment(p, z), y -> initialSegment(p, t))
            )

            have(thesis) by Substitution.apply2(false, lastStep)(domgz)
          }

          // the double initial segment is redundant
          val initPTEqual = have(initialSegment(pt, z) === initialSegment(p, z)) subproof {

            // expand defs
            have(forall(z, (z === initialSegment(x, y)) <=> forall(t, in(t, z) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x)))))) by Weakening(
              initialSegment.definition of (p -> x, a -> y)
            )
            thenHave(forall(t, in(t, initialSegment(x, y)) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x))))) by InstantiateForall(initialSegment(x, y))
            val initXY = thenHave(in(c, initialSegment(x, y)) <=> (in(c, firstInPair(x)) /\ in(pair(c, y), secondInPair(x)))) by InstantiateForall(c)

            // forward
            val fwd = have(in(b, initialSegment(pt, z)) |- in(b, initialSegment(p, z))) subproof {
              assume(in(b, initialSegment(pt, z)))

              have(in(b, firstInPair(pt))) by Tautology.from(initXY of (x -> pt, y -> z, c -> b))
              val bpt = thenHave(in(b, initialSegment(p, t))) by Substitution.apply2(false, firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
              have(in(b, initialSegment(p, t)) ==> in(b, p1)) by Tautology.from(initXY of (x -> p, y -> t, c -> b))
              val bInP1 = have(in(b, p1)) by Tautology.from(lastStep, bpt)

              val bzInP2 = have(in(pair(b, z), p2)) subproof {
                have(in(z, initialSegment(p, t))) by Restate
                val zt = have(in(pair(z, t), p2)) by Tautology.from(lastStep, initXY of (x -> p, y -> t, c -> z))

                have(in(pair(b, z), secondInPair(pt))) by Tautology.from(initXY of (x -> pt, y -> z, c -> b))
                val bzpt = thenHave(in(pair(b, z), initialSegmentOrder(p, t))) by Substitution.apply2(false, secondInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))

                have(thesis) subproof {
                  have(
                    forall(
                      z,
                      (z === initialSegmentOrder(p, t)) <=> forall(a, in(a, z) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
                    )
                  ) by Weakening(initialSegmentOrder.definition of a -> t)
                  thenHave(
                    forall(a, in(a, initialSegmentOrder(p, t)) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
                  ) by InstantiateForall(initialSegmentOrder(p, t))
                  thenHave(
                    in(pair(b, z), initialSegmentOrder(p, t)) <=> (in(pair(b, z), secondInPair(p)) /\ (in(firstInPair(pair(b, z)), initialSegment(p, t)) /\ in(
                      secondInPair(pair(b, z)),
                      initialSegment(p, t)
                    )))
                  ) by InstantiateForall(pair(b, z))
                  have(thesis) by Tautology.from(lastStep, bzpt)
                }
              }
            }

            // backward
            val bwd = have(in(b, initialSegment(p, z)) |- in(b, initialSegment(pt, z))) subproof {
              assume(in(b, initialSegment(p, z)))

              val bpt = have(in(b, initialSegment(p, t))) subproof {
                val bInP1 = have(in(b, p1)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))

                val bz = have(in(pair(b, z), p2)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))
                val zt = have(in(pair(z, t), p2)) by Tautology.from(initXY of (x -> p, y -> t, c -> z))

                have(forall(w, forall(y, forall(z, (in(pair(w, y), p2) /\ in(pair(y, z), p2)) ==> in(pair(w, z), p2))))) by Weakening(wellOrderTransitivity)
                thenHave((in(pair(b, z), p2) /\ in(pair(z, t), p2)) ==> in(pair(b, t), p2)) by InstantiateForall(b, z, t)

                have(in(pair(b, t), p2)) by Tautology.from(lastStep, bz, zt)
                have(thesis) by Tautology.from(lastStep, bInP1, initXY of (x -> p, y -> t, c -> b))
              }

              val bzInP2 = have(in(pair(b, z), initialSegmentOrder(p, t))) subproof {
                have(
                  forall(
                    z,
                    (z === initialSegmentOrder(p, t)) <=> forall(a, in(a, z) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
                  )
                ) by Weakening(initialSegmentOrder.definition of a -> t)
                thenHave(
                  forall(a, in(a, initialSegmentOrder(p, t)) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
                ) by InstantiateForall(initialSegmentOrder(p, t))
                thenHave(
                  in(pair(b, z), initialSegmentOrder(p, t)) <=> (in(pair(b, z), secondInPair(p)) /\ (in(firstInPair(pair(b, z)), initialSegment(p, t)) /\ in(
                    secondInPair(pair(b, z)),
                    initialSegment(p, t)
                  )))
                ) by InstantiateForall(pair(b, z))
                val ordDef = thenHave(in(pair(b, z), initialSegmentOrder(p, t)) <=> (in(pair(b, z), secondInPair(p)) /\ (in(b, initialSegment(p, t)) /\ in(z, initialSegment(p, t))))) by Substitution
                  .apply2(false, firstInPairReduction of (x -> b, y -> z), secondInPairReduction of (x -> b, y -> z))

                val bz = have(in(pair(b, z), p2)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))
                have(thesis) by Tautology.from(ordDef, bz, bpt)
              }

              have(in(b, initialSegment(pt, z)) <=> (in(b, initialSegment(p, t)) /\ in(pair(b, z), initialSegmentOrder(p, t)))) by Substitution.apply2(
                true,
                firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)),
                secondInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t))
              )(initXY of (x -> pt, y -> z, c -> b))
              have(thesis) by Tautology.from(lastStep, bpt, bzInP2)
            }

            // combine
            have(in(b, initialSegment(p, z)) <=> in(b, initialSegment(pt, z))) by Tautology.from(fwd, bwd)
            thenHave(forall(b, in(b, initialSegment(p, z)) <=> in(b, initialSegment(pt, z)))) by RightForall
            have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> initialSegment(p, z), y -> initialSegment(pt, z)))
          }

          // on the restricted domain, app(orderedRestriction(g, z, p), b) = app(g, b)
          val ordApp = have(forall(b, in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b)))) subproof {
            // b < z ==> g_z(b) = g(b)
            val bToApp = have(in(b, initialSegment(p, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b))) subproof {
              have(in(b, initialSegment(p, z)) ==> (app(restrictedFunction(g, initialSegment(p, z)), b) === app(g, b))) by Tautology.from(
                restrictedFunctionApplication of (f -> g, x -> initialSegment(p, z), y -> b)
              )
              thenHave(thesis) by Substitution.apply2(true, ordResDef)
            }

            // b <_t z ==> b < z
            val btTobz = have(in(b, initialSegment(pt, z)) ==> in(b, initialSegment(p, z))) subproof {
              have(in(b, initialSegment(pt, z)) ==> in(b, initialSegment(pt, z))) by Restate
              thenHave(thesis) by Substitution.apply2(false, initPTEqual)
            }

            // so b <_t z ==> g_z(b) = g(b)
            have(in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b))) by Tautology.from(bToApp, btTobz)

            // quantify
            thenHave(thesis) by RightForall
          }

          // for every element in the restricted domain, g1_z(b)  = g2_z(b)
          val eqOnDom = have(forall(b, in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b)))) subproof {
            val unquantified = have(in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b))) subproof {
              assume(in(b, initialSegment(pt, z)))

              val instOrd = have((app(orderedRestriction(g, z, p), b) === app(g, b))) by InstantiateForall(b)(ordApp)

              val eqTg2zg1 = equalityTransitivity of (x -> app(orderedRestriction(g2, z, p), b), y -> app(orderedRestriction(g1, z, p), b), z -> app(g1, b))
              val eqTg1g2 = equalityTransitivity of (x -> app(orderedRestriction(g2, z, p), b), y -> app(g2, b), z -> app(g1, b))

              have(app(g1, b) === app(g2, b))
              have(thesis) by Tautology.from(lastStep, instOrd of g -> g1, instOrd of g -> g2, eqTg2zg1, eqTg1g2)
            }

            thenHave(thesis) by RightForall
          }

          // but then g1_z = g2_z
          val orderedRestrictionsEqual = have(orderedRestriction(g1, z, p) === orderedRestriction(g2, z, p)) subproof {
            have(fun(g, t) |- functionalOver(orderedRestriction(g, z, p), initialSegment(p, z))) by Restate.from(restrictionIsFunction)

            // but initialSegment pt z = initialSegment p z
            val fung = thenHave(fun(g, t) |- functionalOver(orderedRestriction(g, z, p), initialSegment(pt, z))) by Substitution.apply2(true, initPTEqual)

            have(thesis) by Tautology.from(
              fung of g -> g1,
              fung of g -> g2,
              eqOnDom,
              functionsEqualIfEqualOnDomain of (f -> orderedRestriction(g1, z, p), g -> orderedRestriction(g2, z, p), a -> initialSegment(pt, z))
            )
          }

          // and thus F(g1_z) = F(g2_z)
          val fg1g2eq = have(F(orderedRestriction(g1, z, p)) === F(orderedRestriction(g2, z, p))) subproof {
            have(F(orderedRestriction(g1, z, p)) === F(orderedRestriction(g1, z, p))) by Restate
            thenHave(thesis) by Substitution.apply2(false, orderedRestrictionsEqual)
          }

          // but then app(g1, z) = F (g1_z) = F(g1_z) = app(g2, z)
          have(thesis) subproof {
            val gzf = have(fun(g, t) |- app(g, z) === F(orderedRestriction(g, z, p))) subproof {
              assume(fun(g, t))
              have(forall(a, in(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p))))) by Restate
              thenHave(in(z, initialSegment(p, t)) ==> (app(g, z) === F(orderedRestriction(g, z, p)))) by InstantiateForall(z)
              thenHave(thesis) by Tautology
            }

            // g1(z) = F(g1_z)
            val g1f = gzf of g -> g1

            // g2(z) = F(g2_z)
            val g2f = gzf of g -> g2

            // F(g1_z) = F(g2_z)
            // fg1g2eq

            val fg1fg2Tog1 = equalityTransitivity of (x -> F(orderedRestriction(g1, z, p)), y -> F(orderedRestriction(g2, z, p)), z -> app(g1, z))
            val g2fg2Tog1 = equalityTransitivity of (x -> app(g2, z), y -> F(orderedRestriction(g2, z, p)), z -> app(g1, z))

            // g1(z) = g2(z)
            have(thesis) by Tautology.from(fg1fg2Tog1, g2fg2Tog1, g1f, g2f, fg1g2eq)
          }
        }

        // thus, they must agree on the whole domain
        val eqZ = have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- forall(z, in(z, initialSegment(p, t)) ==> (app(g1, z) === app(g2, z)))) subproof {
          assume(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))
          have(in(z, initialSegment(p, t)) |- forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))) by Weakening(
            initToz
          )
          thenHave(
            in(z, firstInPair(pt)) |- forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))
          ) by Substitution.apply2(true, firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
          thenHave(
            in(z, firstInPair(pt)) ==> (forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z)))
          ) by Restate
          thenHave(
            forall(z, in(z, firstInPair(pt)) ==> (forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))))
          ) by RightForall
          have(
            forall(z, in(z, firstInPair(pt)) ==> (app(g1, z) === app(g2, z)))
          ) by Tautology.from(lastStep, ptWO, wellOrderedInduction of (p -> pt, Q -> lambda(x, app(g1, x) === app(g2, x))))
          thenHave(thesis) by Substitution.apply2(false, firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
        }

        // so g1 = g2, but this is a contradiction
        val contra = have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- ()) subproof {
          assume(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))
          have((g1 === g2)) by Tautology.from(eqZ, functionsEqualIfEqualOnDomain of (f -> g1, g -> g2, a -> initialSegment(p, t)))
          thenHave(thesis) by Restate
        }

        // so there exists a unique one, if there exists one at all
        have(!exists(g, fun(g, t)) \/ existsOne(g, fun(g, t))) subproof {
          have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- ()) by Restate.from(contra)
          thenHave(exists(g2, fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2)) |- ()) by LeftExists
          thenHave(exists(g1, exists(g2, fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))) |- ()) by LeftExists
          have(thesis) by Tautology.from(lastStep, atleastTwoExist of (P -> lambda(x, fun(x, t))))
        }

        thenHave(thesis) by Restate
      }

      // EXISTENCE ----------------------------------------
      // if there exists a unique g for the initial segment, get the set of these
      val wDef = forall(t, in(t, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(t, y)))
      // take its union
      // this is a function g for x (almost)
      val uw = union(w) // + (predecessor x, F(U w)) in the successor case

      val v = setUnion(union(uw), singleton(pair(x, F(uw))))

      // need to show:
      //   - uw is a function as required over the initial segment of x
      //   - (x, F(Uw)) is a function
      //   - v = uw + (x, F(Uw)) is a function over p_1 <= x
      //   - v satisfies the fun property
      //   - so x satisfies the prop property

      // we first show the restricted existence version of prop
      val gExists = have(exists(g, fun(g, x))) subproof {
        have(wDef |- fun(v, x)) subproof {
          assume(wDef)
          // properties of the elements of w
          // 1. t \in w ==> functional t
          // 2. t1, t2 \in w ==> t1 \subseteq t2 \/ t2 \subseteq t1

          // 1. t \in w ==> functional t
          val elemsFunctional = have(forall(t, in(t, w) ==> functional(t))) subproof {
            have(in(t, w) |- functional(t)) subproof {
              assume(in(t, w))
              have(in(t, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(t, y))) by InstantiateForall
              val exy = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(t, y))) by Tautology

              have(exists(y, in(y, initialSegment(p, x)) /\ fun(t, y)) |- functional(t)) subproof {
                have(fun(t, y) |- functional(t)) by Tautology.from(functionalOver.definition of (f -> t, x -> initialSegmentLeq(p, y)))
                thenHave((in(y, initialSegment(p, x)) /\ fun(t, y)) |- functional(t)) by Weakening
                thenHave(thesis) by LeftExists
              }
            }
            thenHave(in(t, w) ==> functional(t)) by Restate
            thenHave(thesis) by RightForall
          }

          val t1 = variable
          val t2 = variable

          val elemsSubset = have(forall(t1, forall(t2, (in(t1, w) /\ in(t2, w)) ==> (subset(t1, t2) \/ subset(t2, t1))))) subproof {
            have(in(t1, w) /\ in(t2, w) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
              assume(in(t1, w))
              assume(in(t2, w))

              // given t1 and t2
              // they must come from y1 and y2

              // if t1 == t2
              // done
              have((t1 === t2) |- subset(t1, t2) \/ subset(t2, t1)) by Weakening(subsetEqualitySymmetry of (x -> t1, y -> t2))

              // if t1 != t2
              have(!(t1 === t2) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
                assume(!(t1 === t2))
                def ytDef(y: Term, t: Term) = in(y, initialSegment(p, x)) /\ fun(t, y)
                val y1 = variable
                val y2 = variable

                have(ytDef(y1, t1) /\ ytDef(y2, t2) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
                  assume(ytDef(y1, t1))
                  assume(ytDef(y2, t2))
                  // cases:
                  // y1 == y2
                  // done by the uniqueness lemma above
                  val yeq = have((y1 === y2) |- subset(t1, t2)) subproof {
                    assume(y1 === y2)
                    have(fun(t1, y1) /\ fun(t2, y2)) by Restate
                    thenHave(fun(t1, y1) /\ fun(t2, y1)) by RightSubstEq.apply2
                    thenHave(fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2)) by Restate
                    thenHave(exists(t2, fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2))) by RightExists
                    thenHave(exists(t1, exists(t2, fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2)))) by RightExists
                    have(exists(t1, fun(t1, y1)) /\ !existsOne(t1, fun(t1, y1))) by Tautology.from(lastStep, atleastTwoExist of P -> lambda(t1, fun(t1, y1)))
                    have(bot()) by Tautology.from(lastStep, gUnique of t -> t1)
                  }

                  // y1 != y2
                  // real work to be done here :-
                  val neq = have(!(y1 === y2) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
                    assume(!(y1 === y2))

                    // y1 < y2 or y2 < y1?
                    // we prove it in the generic case
                    val a1 = variable
                    val a2 = variable
                    val k1 = variable
                    val k2 = variable
                    val ltToSubset = have(ytDef(a1, k1) /\ ytDef(a2, k2) /\ in(pair(a1, a2), p2) |- subset(k1, k2)) subproof {
                      assume(ytDef(a1, k1))
                      assume(ytDef(a2, k2))
                      assume(in(pair(a1, a2), p2))
                      // fun(k1, a1)
                      // fun(k2, a2)
                      // a1 < a2
                      // we should have k1 \subseteq k2

                      // dom k1 \subseteq dom k2
                      val domSubset =
                        have(subset(initialSegmentLeq(p, a1), initialSegmentLeq(p, a2))) by Tautology.from(initialSegmentsSubset of (x -> a1, y -> a2), wellOrder.definition, totalOrder.definition)

                      // suppose there is a minimal n such that k1 n != k2 n
                      val n = variable
                      val nDef =
                        in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(b, (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b)))

                      // if k1 and k2 disagree at all
                      val k1k2disagree = exists(n, in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))

                      val nExists = have(k1k2disagree |- exists(n, nDef)) subproof {
                        assume(k1k2disagree)

                        // B defined by x => x < a1 /\ k1 x != k2 x exists
                        val B = variable
                        val BDef = forall(x, in(x, B) <=> (in(x, initialSegment(p, a1)) /\ !(app(k1, x) === app(k2, x))))
                        val BExists = have(exists(B, BDef)) by Weakening(comprehensionSchema of (z -> initialSegment(p, a1), sPhi -> lambda(Seq(x, z), !(app(k1, x) === app(k2, x)))))

                        // B forms a subset of p1
                        val subsetB = have(BDef |- subset(B, p1)) subproof {
                          assume(BDef)
                          have(in(x, B) <=> (in(x, initialSegment(p, a1)) /\ !(app(k1, x) === app(k2, x)))) by InstantiateForall
                          have(in(x, B) ==> in(x, p1)) by Tautology.from(lastStep, initialSegment.definition of a -> a1)
                          thenHave(forall(x, in(x, B) ==> in(x, p1))) by RightForall
                          have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> B, y -> p1))
                        }

                        // B is non-empty
                        val nonEmptyB = have(BDef |- !(B === emptySet())) subproof {
                          assume(BDef)
                          have(in(x, B) <=> (in(x, initialSegment(p, a1)) /\ !(app(k1, x) === app(k2, x)))) by InstantiateForall
                          thenHave((in(x, initialSegment(p, a1)) /\ !(app(k1, x) === app(k2, x))) |- in(x, B)) by Weakening
                          have((in(x, initialSegment(p, a1)) /\ !(app(k1, x) === app(k2, x))) |- !(B === emptySet())) by Cut(lastStep, setWithElementNonEmpty of (y -> x, x -> B))
                          thenHave(thesis) by LeftExists
                        }

                        // so it has a minimal element
                        val minimalB = have(BDef |- exists(n, nDef)) subproof {
                          assume(BDef)
                          have(forall(B, (subset(B, p1) /\ !(B === emptySet())) ==> exists(n, in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b)))))) by Tautology.from(
                            wellOrder.definition
                          )
                          thenHave((subset(B, p1) /\ !(B === emptySet())) ==> exists(n, in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))))) by InstantiateForall(B)
                          val exN = have(exists(n, in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))))) by Tautology.from(lastStep, nonEmptyB, subsetB)

                          // transform n \in B to n < a1 /\ k1 n != k2 n
                          have(in(b, B) <=> (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b)))) by InstantiateForall
                          thenHave(
                            (in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))) <=> ((in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b)))
                          ) by Tautology
                          thenHave(
                            forall(b, (in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))) <=> ((in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))))
                          ) by RightForall
                          val bEq = have(
                            forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))) <=> forall(
                              b,
                              (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                            )
                          ) by Tautology.from(
                            lastStep,
                            universalEquivalenceDistribution of (P -> lambda(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))), Q -> lambda(
                              b,
                              (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                            ))
                          )

                          have(in(n, B) <=> (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))) by InstantiateForall
                          have(
                            (in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b)))) <=> (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(
                              b,
                              (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                            ))
                          ) by Tautology.from(lastStep, bEq)
                          thenHave(
                            forall(
                              n,
                              (in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b)))) <=> (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(
                                b,
                                (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                              ))
                            )
                          ) by RightForall

                          have(thesis) by Tautology.from(
                            lastStep,
                            exN,
                            existentialEquivalenceDistribution of (P -> lambda(n, (in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))))), Q -> lambda(
                              n,
                              (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(
                                b,
                                (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                              ))
                            ))
                          )
                        }

                        thenHave(exists(B, BDef) |- exists(n, nDef)) by LeftExists
                        have(thesis) by Cut(BExists, lastStep)
                      }

                      // but k1 n == F(k1 |^ n) and k2 n == F(k2 |^ n)
                      val fK1 = have(nDef |- app(k1, n) === F(orderedRestriction(k1, n, p))) subproof {
                        // n < a1 ==> k1 n = F(k1 |^ n)
                        have(forall(b, in(b, initialSegment(p, a1)) ==> (app(k1, b) === F(orderedRestriction(k1, b, p))))) by Tautology
                        thenHave(in(n, initialSegment(p, a1)) ==> (app(k1, n) === F(orderedRestriction(k1, n, p)))) by InstantiateForall(n)

                        // we know n < a1, so result
                        thenHave(thesis) by Tautology
                      }
                      val fK2 = have(nDef |- app(k2, n) === F(orderedRestriction(k2, n, p))) subproof {
                        // n < a2 ==> k2 n = F(k2 |^ n)
                        have(forall(b, in(b, initialSegment(p, a2)) ==> (app(k2, b) === F(orderedRestriction(k2, b, p))))) by Tautology
                        val impl = thenHave(in(n, initialSegment(p, a2)) ==> (app(k2, n) === F(orderedRestriction(k2, n, p)))) by InstantiateForall(n)

                        // n < a1 and a1 < a2, so n < a2
                        have(forall(b, in(b, initialSegment(p, a1)) ==> in(b, initialSegment(p, a2)))) by Tautology.from(
                          domSubset,
                          subsetAxiom of (x -> initialSegment(p, a1), y -> initialSegment(p, a2))
                        )
                        thenHave(in(n, initialSegment(p, a1)) ==> in(n, initialSegment(p, a2))) by InstantiateForall(n)

                        // so result
                        have(thesis) by Tautology.from(lastStep, impl)
                      }

                      // k1 |^ n  == k2 |^ n by minimality of n
                      // so F(k1 |^ n) == F(k2 |^ n)
                      val ordResEq = have(nDef |- F(orderedRestriction(k1, n, p)) === F(orderedRestriction(k2, n, p))) subproof {
                        assume(nDef)

                        val k1k2 = have(orderedRestriction(k1, n, p) === orderedRestriction(k2, n, p)) subproof {
                          // suppose not
                          assume(!(orderedRestriction(k1, n, p) === orderedRestriction(k2, n, p)))

                          // there must exist an element where they disagree, say m
                          val m = variable
                          val mDef = in(m, initialSegment(p, n)) /\ !(app(k1, m) === app(k1, m))
                          val mExists = have(exists(m, mDef)) subproof {
                            // k1 |^ n != k2 |^ n by assumption
                            val unequal = have(!(orderedRestriction(k1, n, p) === orderedRestriction(k2, n, p))) by Restate

                            // they are functions on the same domain
                            val functional = have(functionalOver(orderedRestriction(k1, n, p), initialSegment(p, n)) /\ functionalOver(orderedRestriction(k2, n, p), initialSegment(p, n))) by Tautology
                              .from(orderedRestrictionFunctionalOverInit of (f -> k1, a -> n), orderedRestrictionFunctionalOverInit of (f -> k2, a -> n))

                            // so there is a violating element
                            have(!forall(m, in(m, initialSegment(p, n)) ==> (app(k1, m) === app(k2, m)))) by Tautology.from(
                              unequal,
                              functional,
                              functionsEqualIfEqualOnDomain of (f -> k1, g -> k2, a -> initialSegment(p, n))
                            )
                            thenHave(thesis) by Restate
                          }

                          // we must have m < n
                          val mViolates = have(mDef |- in(m, initialSegment(p, a1)) /\ !(app(k1, m) === app(k1, m)) /\ in(pair(m, n), p2)) subproof {
                            // we have n < a1
                            have(forall(z, (z === initialSegment(p, a)) <=> (forall(t, in(t, z) <=> (in(t, p1) /\ in(pair(t, a), p2)))))) by Weakening(initialSegment.definition)
                            val initSegMembership = thenHave((forall(t, in(t, initialSegment(p, a)) <=> (in(t, p1) /\ in(pair(t, a), p2))))) by InstantiateForall(initialSegment(p, a))

                            have(in(n, initialSegment(p, a1)) <=> (in(n, p1) /\ in(pair(n, a1), p2))) by InstantiateForall(n)(initSegMembership of a -> a1)
                            val nLTa1 = thenHave(in(pair(n, a1), p2)) by Tautology

                            // and m < n
                            have(in(m, initialSegment(p, n)) <=> (in(m, p1) /\ in(pair(m, n), p2))) by InstantiateForall(m)(initSegMembership of a -> n)
                            val mLTn = thenHave(in(m, p1) /\ in(pair(m, n), p2)) by Tautology

                            // by transitivity, m < a1 as well
                            have(forall(w, forall(y, forall(z, (in(pair(w, y), p2) /\ in(pair(y, z), p2)) ==> in(pair(w, z), p2))))) by Weakening(wellOrderTransitivity)
                            thenHave((in(pair(m, n), p2) /\ in(pair(n, a1), p2)) ==> in(pair(m, a1), p2)) by InstantiateForall(m, n, a1)
                            val mLTa1 = have(in(m, p1) /\ in(pair(m, a1), p2)) by Tautology.from(lastStep, nLTa1, mLTn)

                            have(in(m, initialSegment(p, a1)) <=> (in(m, p1) /\ in(pair(m, a1), p2))) by InstantiateForall(m)(initSegMembership of a -> a1)
                            have(thesis) by Tautology.from(lastStep, mLTa1)
                          }

                          // but n was the minimal violation
                          // contradiction
                          have(bot()) subproof {
                            // m < a1 and k1 m != k2 m ==> n < m \/ n = m
                            have(forall(b, (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b)))) by Restate
                            have((in(m, initialSegment(p, a1)) /\ !(app(k1, m) === app(k2, m))) ==> (in(pair(n, m), p2) \/ (n === m))) by InstantiateForall
                            have((in(pair(n, m), p2) \/ (n === m)))

                            // we had m < n, and the order is anti-symmetric, so n = m
                            have(forall(n, forall(m, (in(pair(m, n), p2) /\ in(pair(n, m), p2)) ==> (n === m)))) by Tautology.from(
                              wellOrder.definition,
                              totalOrder.definition,
                              partialOrder.definition,
                              antiSymmetric.definition of (r -> p2, x -> p1)
                            )
                            thenHave((in(pair(m, n), p2) /\ in(pair(n, m), p2)) ==> (n === m)) by InstantiateForall(n, m)
                            val nEQm = have((n === m)) by Tautology.from(lastStep, mViolates)

                            // however, that means n < n, but the order is anti-reflexive
                            have(in(pair(m, n), p2)) by Weakening(mViolates)
                            val nLTn = thenHave(in(pair(n, n), p2)) by Substitution.apply2(true, nEQm)

                            have(forall(n, !in(pair(n, n), p2))) by Tautology.from(wellOrder.definition, totalOrder.definition, partialOrder.definition, antiReflexive.definition of (r -> p2, x -> p1))
                            thenHave(!in(pair(n, n), p2)) by InstantiateForall(n)

                            // this is a contradiction
                            have(thesis) by Tautology.from(lastStep, nLTn)
                          }
                        }

                        have(F(orderedRestriction(k1, n, p)) === F(orderedRestriction(k1, n, p))) by Restate
                        thenHave(thesis) by Substitution.apply2(false, k1k2)
                      }

                      // finally k1 n == k2 n
                      // this is a contradiction
                      val appEq = have(app(k1, n) === app(k2, n)) subproof {
                        val k1ToFK2 = equalityTransitivity of (x -> app(k1, n), y -> F(orderedRestriction(k1, n, p)), z -> F(orderedRestriction(k2, n, p)))
                        val k1ToK2 = equalityTransitivity of (x -> app(k1, n), y -> F(orderedRestriction(k2, n, p)), z -> app(k2, n))

                        have(thesis) by Tautology.from(fK1, fK2, ordResEq, k1ToFK2, k1ToK2)
                      }

                      thenHave(nDef |- ()) by Tautology
                      thenHave(exists(n, nDef) |- ()) by LeftExists
                      have(thesis) by Tautology.from(lastStep, nExists)
                    }

                    val y1LTy2 = have(in(pair(y1, y2), p2) |- subset(t1, t2)) by Restate.from(ltToSubset of (a1 -> y1, k1 -> t1, a2 -> y2, k2 -> t2))
                    val y2LTy1 = have(in(pair(y2, y1), p2) |- subset(t2, t1)) by Restate.from(ltToSubset of (a1 -> y2, k1 -> t2, a2 -> y1, k2 -> t1))

                    // totality of the order means y1 < y2 or y2 < y1
                    have(in(pair(y1, y2), p2) \/ in(pair(y2, y1), p2)) subproof {
                      have(forall(y1, forall(y2, (in(y1, p1) /\ in(y2, p1)) ==> (in(pair(y1, y2), p2) \/ in(pair(y2, y1), p2) \/ (y1 === y2))))) by Tautology.from(
                        wellOrder.definition,
                        total.definition of (r -> p2, x -> p1)
                      )
                      val impl = thenHave((in(y1, p1) /\ in(y2, p1)) ==> (in(pair(y1, y2), p2) \/ in(pair(y2, y1), p2) \/ (y1 === y2))) by InstantiateForall(y1, y2)

                      // expand defs
                      have(forall(z, (z === initialSegment(x, y)) <=> forall(t, in(t, z) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x)))))) by Weakening(
                        initialSegment.definition of (p -> x, a -> y)
                      )
                      thenHave(forall(t, in(t, initialSegment(x, y)) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x))))) by InstantiateForall(initialSegment(x, y))
                      val initXY = thenHave(in(c, initialSegment(x, y)) <=> (in(c, firstInPair(x)) /\ in(pair(c, y), secondInPair(x)))) by InstantiateForall(c)

                      have(in(y1, p1) /\ in(y2, p1)) by Tautology.from(initXY of (x -> p, y -> x, c -> y1), initXY of (x -> p, y -> x, c -> y2))
                      have(thesis) by Tautology.from(lastStep, impl)
                    }

                    have(thesis) by Tautology.from(lastStep, y1LTy2, y2LTy1)
                  }
                }

                thenHave((ytDef(y1, t1), ytDef(y2, t2)) |- subset(t1, t2) \/ subset(t2, t1)) by Restate
                thenHave((ytDef(y1, t1), exists(y, ytDef(y, t2))) |- subset(t1, t2) \/ subset(t2, t1)) by LeftExists
                val exToRes = thenHave((exists(y, ytDef(y, t1)), exists(y, ytDef(y, t2))) |- subset(t1, t2) \/ subset(t2, t1)) by LeftExists

                val exy = have(in(a, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(a, y))) by InstantiateForall

                have(thesis) by Tautology.from(exToRes, exy of a -> t1, exy of a -> t2)
              }
            }

            sorry
          }

          val uwfunctional = have(functional(uw)) by Tautology.from(elemsFunctional, elemsSubset, unionOfFunctionSet of z -> w)
          val uwdomain = have(functionalOver(uw, initialSegment(p, x)))

          val pairFunctional = have(functionalOver(singleton(pair(x, F(uw))), singleton(x))) subproof {
            sorry
          }

          val initialSegmentToLeq = have(setUnion(initialSegment(p, x), singleton(x)) === initialSegmentLeq(p, x)) by Sorry

          val vFunctionalOver = have(functionalOver(v, initialSegmentLeq(p, x))) by Sorry

          val vRecursive = have(forall(a, in(a, initialSegmentLeq(p, x)) ==> (app(v, a) === F(orderedRestriction(v, a, p))))) by Sorry

          have(thesis) by Tautology.from(vFunctionalOver, vRecursive)
        }

        thenHave(wDef |- exists(g, fun(g, x))) by RightExists
        val funExists = thenHave(exists(w, wDef) |- exists(g, fun(g, x))) by LeftExists

        have(exists(w, wDef)) by Sorry

        have(thesis) by Cut(lastStep, funExists)
      }

      have(thesis) by Tautology.from(gExists, gUnique of t -> x)
    }

    thenHave(forall(x, in(x, p1) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x)))) by RightForall
    have(thesis) by Tautology.from(lastStep, wellOrderedInduction of Q -> lambda(x, prop(x)))
  }
  show

  val transfiniteRecursion = Theorem(
    ordinal(a) |- existsOne(g, functionalOver(g, a) /\ forall(b, in(b, a) ==> (app(g, b) === F(restrictedFunction(g, b)))))
  ) {
    sorry
  }

}
