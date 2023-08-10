package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.FirstOrderLogic.existsOneImpliesExists
import lisa.mathematics.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.utils.Printer

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
   * Partial Order --- `p` is a partial order on `x` if it is a pair `(x, r)`,
   * and `r` is a [[reflexive]] and [[transitive]] binary [[relation]] on `x`.
   */
  val partialOrder = DEF(p) --> relationBetween(secondInPair(p), firstInPair(p), firstInPair(p)) /\ antiReflexive(secondInPair(p), firstInPair(p)) /\ transitive(secondInPair(p), firstInPair(p))

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
        thenHave((in(y, x), b === y, c === x) |- in(b, c)) by Substitution.withExplicitRules(b === y, c === x)
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
    val subs = thenHave(subset(inclusionOn(a), cartesianProduct(a, a))) by Substitution.withExplicitRules(subsetAxiom of (x -> inclusionOn(a), y -> cartesianProduct(a, a)))

    have(thesis) by Tautology.from(subs, relationBetween.definition of (r -> inclusionOn(a), a -> a, b -> a))
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
    thenHave(thesis) by Substitution.withExplicitRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is an irreflexive relation.
   */
  val emptyInclusionIrreflexive = Lemma(
    () |- irreflexive(inclusionOn(emptySet()), a)
  ) {
    have(irreflexive(emptySet(), a)) by Restate.from(emptyRelationIrreflexive)
    thenHave(thesis) by Substitution.withExplicitRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is a transitive relation.
   */
  val emptyInclusionTransitive = Lemma(
    () |- transitive(inclusionOn(emptySet()), a)
  ) {
    have(transitive(emptySet(), a)) by Restate.from(emptyRelationTransitive)
    thenHave(thesis) by Substitution.withExplicitRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the empty relation partially orders the empty set
   */
  val emptySetPartialOrder = Lemma(
    () |- partialOrder(pair(emptySet(), emptySet()))
  ) {
    have(
      partialOrder(pair(emptySet(), emptySet())) <=> (relationBetween(emptySet(), emptySet(), emptySet()) /\ antiReflexive(emptySet(), emptySet()) /\ transitive(emptySet(), emptySet()))
    ) by Substitution.withExplicitRules(firstInPairReduction of (x -> emptySet(), y -> emptySet()), secondInPairReduction of (x -> emptySet(), y -> emptySet()))(
      partialOrder.definition of p -> pair(emptySet(), emptySet())
    )
    have(thesis) by Tautology.from(lastStep, emptySetRelationOnItself, emptyRelationIrreflexive of a -> emptySet(), emptyRelationTransitive of a -> emptySet())
  }

  /**
   * Theorem --- the empty relation totally orders the empty set
   */
  val emptySetTotalOrder = Lemma(
    () |- totalOrder(pair(emptySet(), emptySet()))
  ) {
    have(totalOrder(pair(emptySet(), emptySet())) <=> (partialOrder(pair(emptySet(), emptySet())) /\ total(emptySet(), emptySet()))) by Substitution.withExplicitRules(
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
    ) by Substitution.withExplicitRules(firstInPairReduction of (x -> emptySet(), y -> emptySet()))(wellOrder.definition of p -> pair(emptySet(), emptySet()))

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
        thenHave((forall(y, in(y, x) ==> subset(y, x)), in(y, x)) |- forall(z, in(z, y) ==> in(z, x))) by Substitution.withExplicitRules(subsetAxiom of (x -> y, y -> x))
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
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- subset(y, x)) by Substitution.withExplicitRules(subsetAxiom of (x -> y, y -> x))
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- in(y, x) ==> subset(y, x)) by Restate
        thenHave(thesis) by RightForall
      }

      have(thesis) by Tautology.from(lhs, rhs)
    }

    have(thesis) by Tautology.from(lastStep, transitiveSet.definition)
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
    have(wellOrder(pair(emptySet(), inclusionOn(emptySet())))) by Substitution.withExplicitRules(emptySetInclusionEmpty)(emptySetWellOrder)
    thenHave(thesis) by Substitution.withExplicitRules(incDef)
  }

  /**
   * Theorem --- the empty set is an ordinal (zero).
   */
  val emptySetOrdinal = Theorem(
    () |- ordinal(emptySet())
  ) {
    have(thesis) by Tautology.from(emptySetWellOrderedByInclusion, emptySetTransitive, ordinal.definition of (a -> emptySet()))
  }

  val ordinalsHeredetarilyTransitive = Lemma(
    ordinal(a) |- transitiveSet(a) /\ forall(b, in(b, a) ==> transitiveSet(b))
  ) {
    val ordinalTrans = have(ordinal(a) |- transitiveSet(a)) by Weakening(ordinal.definition)
    val wellOrdInca = have(ordinal(a) |- wellOrder(inclusionOrderOn(a))) by Weakening(ordinal.definition)
    have(inclusionOrderOn(a) === pair(a, inclusionOn(a))) by InstantiateForall(inclusionOrderOn(a))(inclusionOrderOn.definition)
    val wellOrda = have(ordinal(a) |- wellOrder(pair(a, inclusionOn(a)))) by Substitution.withExplicitRules(lastStep)(wellOrdInca)

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
        .withExplicitRules(secondInPairReduction of (x -> a, y -> inclusionOn(a)))(wellOrderTransitivity of p -> pair(a, inclusionOn(a)))
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
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a))), in(b, a)) |- transitiveSet(b)) by Substitution.withExplicitRules(transitiveSetInclusionDef of x -> b)
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a)))) |- in(b, a) ==> transitiveSet(b)) by Restate
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a)))) |- forall(b, in(b, a) ==> transitiveSet(b))) by RightForall

    have(thesis) by Tautology.from(lastStep, wellOrda, ordinalTrans)
  }

  // val elementsOfOrdinalsAreOrdinals = Theorem(
  //   (ordinal(a), in(b, a)) |- ordinal(b)
  // ) {
  //   ???
  // }

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

  // initial segment of well order is well ordered under the restricted

  val orderedRestrictionUniqueness = Lemma(
    () |- existsOne(g, forall(t, in(t, g) <=> (in(t, f) /\ in(pair(firstInPair(t), a), secondInPair(p)))))
  ) {
    have(thesis) by UniqueComprehension(f, lambda(Seq(t, f), in(pair(firstInPair(t), a), secondInPair(p))))
  }

  /**
   * The restriction of a function `f` with respect to `a` relative to a
   * partial order `p = (X, <)`. The result is `f` with its domain restricted
   * to the elements less than `a` wrt `<`.
   */
  val orderedRestriction = DEF(f, a, p) --> {
    val `<p` = secondInPair(p)
    The(g, forall(t, in(t, g) <=> (in(t, f) /\ in(pair(firstInPair(t), a), `<p`))))(orderedRestrictionUniqueness)
  }

  /**
   * Theorem --- Well-Ordered Recursion (stronger version)
   */
  // val wellOrderedRecursionStronger = Lemma(
  //   wellOrder(p) |- forall(
  //     t,
  //     in(t, firstInPair(p)) ==> existsOne(g, functionalOver(g, initialSegmentLeq(p, t)) /\ forall(a, in(a, initialSegmentLeq(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p)))))
  //   )
  // ) {

  //   val p1 = firstInPair(p)

  //   def prop(t: Term): Formula = in(t, p1) ==> existsOne(g, functionalOver(g, initialSegmentLeq(p, t)) /\ forall(a, in(a, initialSegmentLeq(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p)))))

  //   // define `z` as the set of elements of `p_1` for which `prop` does not hold
  //   val zDef = forall(t, in(t, z) <=> (in(t, p1) /\ !prop(t)))

  //   // Case 1
  //   // `z` is empty
  //   val case1 = have((zDef, forall(t, !in(t, z))) |- forall(t, prop(t))) subproof {
  //     val zDefInst = have(zDef |- in(t, z) <=> (in(t, p1) /\ !prop(t))) by InstantiateForall
  //     have(forall(t, !in(t, z)) |- !in(t, z)) by InstantiateForall

  //     have((zDef, forall(t, !in(t, z))) |- prop(t)) by Tautology.from(zDefInst, lastStep)
  //     thenHave(thesis) by RightForall
  //   }

  //   // Case 2
  //   // `z` is non-empty
  //   // we lead the proof to a contradiction
  //   val case2 = have((zDef, exists(t, in(t, z)), ???) |- forall(t, prop(t))) subproof {
  //     ???
  //   }

  //   have((zDef, ???) |- forall(t, prop(t))) by Tautology.from(case1, case2)
  //   val byCase = thenHave((exists(z, zDef), ???) |- forall(t, prop(t))) by LeftExists

  //   have(existsOne(z, zDef)) by UniqueComprehension(p1, lambda(Seq(t, z), prop(t)))
  //   have(exists(z, zDef)) by Tautology.from(existsOneImpliesExists of P -> lambda(z, zDef))

  //   have(thesis) by Tautology.from(byCase, lastStep)
  // }

  /**
   * Well ordered recursion (for sets) --- ??? TODO: write description
   */
  // val wellOrderRecursion = Theorem(
  //   // well ordered (p_1, <)
  //   // class function f
  //   // |-
  //   // exists a set function g with domain p_1 such that
  //   // \forall a \in p_1, g(a) = f(g |^ a)
  //   wellOrder(p) |- exists(g, functionalOver(g, firstInPair(p)) /\ forall(a, in(a, firstInPair(p)) ==> (app(g, a) === F(orderedRestriction(g, a, p)))))
  // ) {
  //   ???
  // }

}
