package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
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
   * Greatest Lower Bound --- `a` is the greatest lower bound on `y \subseteq x`
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
   * Least Upper Bound --- `a` is the least upper bound on `y \subseteq x` under
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
   * `\∀ x y. x <_p y ==> f(x) <_q f(y)`
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
   * The relation induced by inclusion on a set, noted `\in_a`.
   *
   * `\in_a = {(y, x) \in a * a | y \in x}`
   */
  val inclusionOn = DEF(a) --> The(z, forall(t, in(t, z) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))))(inclusionOnUniqueness)

  /**
   * The partial order `(a, \in_a)` induced by the inclusion relation
   * ([[inclusionOn]]) on a set.
   */
  val inclusionOrderOn = DEF(a) --> pair(a, inclusionOn(a))

  val inclusionOrderElem = Lemma(
    in(b, a) /\ in(c, a) /\ in(b, c) |- in(pair(b, c), inclusionOn(a))
  ) {
    val prodElem = have(in(b, a) /\ in(c, a) /\ in(b, c) |- in(pair(b, c), cartesianProduct(a, a))) subproof {
      have(in(b, a) /\ in(c, a) /\ in(b, c) |- in(b, a) /\ in(c, a)) by Restate
      thenHave(in(b, a) /\ in(c, a) /\ in(b, c) |- in(pair(b, c), cartesianProduct(a, a))) by Substitution.apply2(true, pairInCartesianProduct of (a -> b, b -> c, x -> a, y -> a))
    }

    val existsXY = have(in(b, a) /\ in(c, a) /\ in(b, c) |- exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x))))) subproof {
      have(in(b, a) /\ in(c, a) /\ in(b, c) |- in(b, c) /\ (pair(b, c) === pair(b, c))) by Restate
      thenHave(in(b, a) /\ in(c, a) /\ in(b, c) |- exists(x, in(b, x) /\ (pair(b, c) === pair(b, x)))) by RightExists
      thenHave(in(b, a) /\ in(c, a) /\ in(b, c) |- exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x))))) by RightExists
    }

    val impl = have(((in(pair(b, c), cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x)))))) |- in(pair(b, c), inclusionOn(a))) subproof {
      have(() |- forall(t, in(t, inclusionOn(a)) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(inclusionOn(a))(
        inclusionOn.definition
      )
      // thenHave(() |- forall(t, in(t, inclusionOn(a)) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by Rewrite
      thenHave(() |- in(pair(b, c), inclusionOn(a)) <=> (in(pair(b, c), cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (pair(b, c) === pair(y, x)))))) by InstantiateForall(pair(b, c))
      thenHave(thesis) by Weakening
    }

    have(thesis) by Tautology.from(prodElem, existsXY, impl)
  }
  show

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
  show

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
  show

  val emptyInclusionReflexive = Lemma(
    () |- reflexive(inclusionOn(emptySet()), emptySet())
  ) {
    have(reflexive(emptySet(), emptySet())) by Restate.from(emptyRelationReflexiveOnItself)
    thenHave(thesis) by Substitution.apply2(true, emptySetInclusionEmpty)
  }

  val emptyInclusionIrreflexive = Lemma(
    () |- irreflexive(inclusionOn(emptySet()), a)
  ) {
    have(irreflexive(emptySet(), a)) by Restate.from(emptyRelationIrreflexive)
    thenHave(thesis) by Substitution.apply2(true, emptySetInclusionEmpty)
  }

  val emptyInclusionTransitive = Lemma(
    () |- transitive(inclusionOn(emptySet()), a)
  ) {
    have(transitive(emptySet(), a)) by Restate.from(emptyRelationTransitive)
    thenHave(thesis) by Substitution.apply2(true, emptySetInclusionEmpty)
  }

  val emptyInclusionPartialOrder = Lemma(
    () |- partialOrder(pair(emptySet(), inclusionOn(emptySet())))
  ) {
    ???
  }

  val emptyInclusionTotalOrder = Lemma(
    () |- totalOrder(pair(emptySet(), inclusionOn(emptySet())))
  ) {
    ???
  }

  val emptyInclusionWellOrder = Lemma(
    () |- wellOrder(pair(emptySet(), inclusionOn(emptySet())))
  ) {
    ???
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
  show

  val transitiveSet = DEF(x) --> forall(y, in(y, x) ==> subset(y, x))

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
   *   - if `a` is an ordinal and `b \in a`, then `b` is an ordinal --- [[ordinalInclusionClosure]]
   *   - if `a`, `b` are ordinals and `b \subset a`, then `b \in a` --- [[ordinalSubsetClosure]]
   *   - if `a` and `b` are distinct ordinals, then either `a \subset b` or `b \subset a` --- [[ordinalSOMETHING]] TODO:
   *
   * Other properties
   *
   *   - the ordinals form a proper class --- [[noSetOfOrdinals]]
   */

  val emptySetTransitive = Lemma(
    () |- transitiveSet(emptySet())
  ) {
    val hypo = have(!in(y, emptySet()) |- in(y, emptySet()) ==> subset(y, emptySet())) by Restate
    have(() |- in(y, emptySet()) ==> subset(y, emptySet())) by Cut(emptySetAxiom of (x -> y), hypo)
    thenHave(() |- forall(y, in(y, emptySet()) ==> subset(y, emptySet()))) by RightForall
    andThen(Simplify.once(true, transitiveSet.definition of (x -> emptySet())))
  }
  show

  val emptySetSubsetEmpty = Lemma(
    () |- subset(a, emptySet()) <=> (a === emptySet())
  ) {
    val fwd = have(() |- subset(a, emptySet()) ==> (a === emptySet())) subproof {
      have(subset(a, emptySet()) |- forall(b, in(b, a) ==> in(b, emptySet()))) by Weakening(subsetAxiom of (x -> a, y -> emptySet()))
      val impl = thenHave(subset(a, emptySet()) |- in(b, a) ==> in(b, emptySet())) by InstantiateForall(b)

      have(subset(a, emptySet()) |- !in(b, a)) by Tautology.from(impl, emptySetAxiom of (x -> b))
      val noElem = thenHave(subset(a, emptySet()) |- forall(b, !in(b, a))) by RightForall

      have(subset(a, emptySet()) |- (a === emptySet())) by Cut.withParameters(forall(b, !in(b, a)))(noElem, setWithNoElementsIsEmpty of (x -> a))
    }

    val bwd = have(() |- (a === emptySet()) ==> subset(a, emptySet())) subproof {
      have(() |- subset(emptySet(), emptySet())) by Restate.from(subsetReflexivity of (x -> emptySet()))
      thenHave((emptySet() === a) |- subset(a, emptySet())) by Substitution
    }

    have(thesis) by RightIff(fwd, bwd)
  }
  show

  val emptySetWellOrderedByInclusion = Lemma(
    () |- wellOrder(pair(emptySet(), inclusionOn(emptySet())))
  ) {}

  val emptySetOrdinal = Theorem(
    () |- ordinal(emptySet())
  ) {
    have((subset(b, emptySet()) /\ !(b === emptySet())) |- (subset(b, emptySet()) /\ !(b === emptySet()))) by Hypothesis
    thenHave((subset(b, emptySet()) /\ !(b === emptySet())) |- ((b === emptySet()) /\ !(b === emptySet()))) by Substitution.apply2(false, emptySetSubsetEmpty of (a -> b))
    thenHave(() |- (subset(b, emptySet()) /\ !(b === emptySet())) ==> (exists(z, in(z, b) /\ forall(x, in(x, b) ==> (in(z, x) \/ (z === x)))))) by Weakening
    val wellOrd = thenHave(() |- forall(b, (subset(b, emptySet()) /\ !(b === emptySet())) ==> (exists(z, in(z, b) /\ forall(x, in(x, b) ==> (in(z, x) \/ (z === x))))))) by RightForall

    have(thesis) by Tautology.from(wellOrd, emptySetTransitive, ordinal.definition of (a -> emptySet()))
  }
  show

  val ordinalsHeredetarilyTransitive = Lemma(
    ordinal(a) |- transitiveSet(a) /\ forall(b, in(b, a) ==> transitiveSet(b))
  ) {
    val ordinalTrans = have(ordinal(a) |- transitiveSet(a)) by Weakening(ordinal.definition)

  }

  val elementsOfOrdinalsAreOrdinals = Theorem(
    (ordinal(a), in(b, a)) |- ordinal(b)
  ) {
    ???
  }

  /**
   * Transfinite Recursion
   */

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
   * Well ordered recursion (for sets) --- ??? TODO: write description
   */
  // val wellOrderRecursion = Theorem(
  //   // well ordered (A, <)
  //   // class function f
  //   // |-
  //   // exists a set function g such that
  //   // g(a) = f(g |^ a)
  //   wellOrder(p) |- exists(g, functionalOver(g, firstInPair(p)) /\ forall(a, in(a, firstInPair(p)) ==> (app(g, a) === f(orderedRestriction(g, a, p)))))
  // ) {
  //   ???
  // }

}
