package lisa.mathematics
package settheory
package orderings

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.fol.Quantifiers.*
import lisa.mathematics.settheory.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.prooflib.Substitution
import lisa.utils.FOLPrinter

object PartialOrders extends lisa.Main {

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

  val predecessor = DEF(p, x, y) --> totalOrder(p) /\ in(x, firstInPair(p)) /\ in(y, firstInPair(p)) /\ in(pair(x, y), secondInPair(p)) /\ forall(
    z,
    !(in(pair(x, z), secondInPair(p)) /\ in(pair(z, y), secondInPair(p)))
  )

  val limitElement = DEF(p, x) --> totalOrder(p) /\ in(x, firstInPair(p)) /\ !exists(y, predecessor(p, y, x))

  val successorElement = DEF(p, x) --> totalOrder(p) /\ in(x, firstInPair(p)) /\ exists(y, predecessor(p, y, x))

  val everyElemInTotalOrderLimitOrSuccessor = Lemma(
    totalOrder(p) /\ in(x, firstInPair(p)) |- (limitElement(p, x) \/ successorElement(p, x))
  ) {
    // limit and successor are just negation of each other
    have(thesis) by Tautology.from(successorElement.definition, limitElement.definition)
  }

  val initialSegmentUnionForLimitElementsIsComplete = Lemma(
    totalOrder(p) /\ limitElement(p, x) |- in(pair(t, x), secondInPair(p)) <=> exists(y, in(pair(t, y), secondInPair(p)) /\ in(pair(y, x), secondInPair(p)))
  ) {
    assume(totalOrder(p))
    assume(limitElement(p, x))

    val p1 = firstInPair(p)
    val p2 = secondInPair(p)

    val fwd = have(in(pair(t, x), p2) |- exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2))) subproof {
      assume(in(pair(t, x), p2))
      assume(forall(y, !(in(pair(t, y), p2) /\ in(pair(y, x), p2)))) // assume negated

      have(forall(y, !predecessor(p, y, x))) by Tautology.from(limitElement.definition)
      thenHave(!predecessor(p, t, x)) by InstantiateForall(t)
      val notInp1 = have(!in(t, p1)) by Tautology.from(lastStep, limitElement.definition, predecessor.definition of (x -> t, y -> x)) // y is free here, so instantiate it to x

      val inst = have(!(in(pair(t, y), p2) /\ in(pair(y, x), p2))) by InstantiateForall

      have(in(t, p1)) subproof {
        have(relationBetween(p2, p1, p1)) by Tautology.from(totalOrder.definition, partialOrder.definition)
        have(subset(p2, cartesianProduct(p1, p1))) by Tautology.from(lastStep, relationBetween.definition of (r -> p2, a -> p1, b -> p1))
        have(forall(z, in(z, p2) ==> in(z, cartesianProduct(p1, p1)))) by Tautology.from(lastStep, subsetAxiom of (x -> p2, y -> cartesianProduct(p1, p1)))
        thenHave(in(pair(t, x), cartesianProduct(p1, p1))) by InstantiateForall(pair(t, x))
        have(in(t, p1)) by Tautology.from(lastStep, pairInCartesianProduct of (a -> t, b -> x, x -> p1, y -> p1))
      }

      have(bot()) by Tautology.from(lastStep, notInp1)
    }

    val bwd = have(exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2)) |- in(pair(t, x), p2)) subproof {
      have(in(pair(t, y), p2) /\ in(pair(y, x), p2) |- in(pair(t, x), p2)) subproof {
        // total orders are transitive
        have(forall(t, forall(y, forall(x, (in(pair(t, y), p2) /\ in(pair(y, x), p2)) ==> in(pair(t, x), p2))))) by Tautology.from(
          totalOrder.definition,
          partialOrder.definition,
          transitive.definition of (r -> p2, x -> p1)
        )
        thenHave(thesis) by InstantiateForall(t, y, x)
      }

      thenHave(thesis) by LeftExists
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }
  show

  val initialSegmentUnionForSuccessorElementsIsIncomplete = Lemma(
    totalOrder(p) /\ successorElement(p, x) |- in(pair(t, x), secondInPair(p)) <=> (predecessor(p, t, x) \/ exists(y, in(pair(t, y), secondInPair(p)) /\ in(pair(y, x), secondInPair(p))))
  ) {
    assume(totalOrder(p))
    assume(successorElement(p, x))

    val p1 = firstInPair(p)
    val p2 = secondInPair(p)

    val fwd = have(in(pair(t, x), p2) |- (predecessor(p, t, x) \/ exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2)))) subproof {
      assume(in(pair(t, x), p2))

      // t < x means t, x \in p1
      val txInp1 = have(in(t, p1) /\ in(x, p1)) subproof {
        have(relationBetween(p2, p1, p1)) by Tautology.from(totalOrder.definition, partialOrder.definition)
        have(subset(p2, cartesianProduct(p1, p1))) by Tautology.from(lastStep, relationBetween.definition of (r -> p2, a -> p1, b -> p1))
        have(forall(z, in(z, p2) ==> in(z, cartesianProduct(p1, p1)))) by Tautology.from(lastStep, subsetAxiom of (x -> p2, y -> cartesianProduct(p1, p1)))
        thenHave(in(pair(t, x), cartesianProduct(p1, p1))) by InstantiateForall(pair(t, x))
        have(thesis) by Tautology.from(lastStep, pairInCartesianProduct of (a -> t, b -> x, x -> p1, y -> p1))
      }

      have(predecessor(p, y, x) |- (predecessor(p, t, x) \/ exists(y, in(pair(t, y), secondInPair(p)) /\ in(pair(y, x), secondInPair(p))))) subproof {
        assume(predecessor(p, y, x))

        have(forall(z, !(in(pair(y, z), p2) /\ in(pair(z, x), p2)))) by Tautology.from(predecessor.definition of (x -> y, y -> x))
        thenHave(!(in(pair(y, t), p2) /\ in(pair(t, x), p2))) by InstantiateForall(t)
        val yNLTt = thenHave(!in(pair(y, t), p2)) by Tautology

        have(forall(y, forall(t, (in(y, p1) /\ in(t, p1)) ==> (in(pair(y, t), p2) \/ in(pair(t, y), p2) \/ (y === t))))) by Tautology.from(
          totalOrder.definition,
          total.definition of (r -> p2, x -> p1)
        )
        thenHave((in(y, p1) /\ in(t, p1)) ==> (in(pair(y, t), p2) \/ in(pair(t, y), p2) \/ (y === t))) by InstantiateForall(y, t)
        val cases = have(in(pair(t, y), p2) \/ (y === t)) by Tautology.from(lastStep, predecessor.definition of (x -> y, y -> x), txInp1, yNLTt)

        val ltCase = have(in(pair(t, y), p2) |- (predecessor(p, t, x) \/ exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2)))) subproof {
          have(in(pair(t, y), p2) |- in(pair(t, y), p2) /\ in(pair(y, x), p2)) by Tautology.from(predecessor.definition of (x -> y, y -> x))
          thenHave(in(pair(t, y), p2) |- exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2))) by RightExists
          thenHave(thesis) by Weakening
        }

        val eqCase = have((y === t) |- (predecessor(p, t, x) \/ exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2)))) subproof {
          have(predecessor(p, y, x)) by Restate
          thenHave((y === t) |- predecessor(p, t, x)) by Substitution.ApplyRules(y === t)
          thenHave(thesis) by Weakening
        }

        have(thesis) by Tautology.from(cases, ltCase, eqCase)
      }

      thenHave(exists(y, predecessor(p, y, x)) |- (predecessor(p, t, x) \/ exists(y, in(pair(t, y), secondInPair(p)) /\ in(pair(y, x), secondInPair(p))))) by LeftExists
      have(thesis) by Tautology.from(lastStep, successorElement.definition)
    }

    val bwd = have((predecessor(p, t, x) \/ exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2))) |- in(pair(t, x), p2)) subproof {
      val predCase = have(predecessor(p, t, x) |- in(pair(t, x), p2)) by Tautology.from(predecessor.definition of (x -> t, y -> x))
      have(in(pair(t, y), p2) /\ in(pair(y, x), p2) |- in(pair(t, x), p2)) subproof {
        // transitivity of p
        have(forall(t, forall(y, forall(x, (in(pair(t, y), p2) /\ in(pair(y, x), p2)) ==> in(pair(t, x), p2))))) by Tautology.from(
          totalOrder.definition,
          partialOrder.definition,
          transitive.definition of (r -> p2, x -> p1)
        )
        thenHave(thesis) by InstantiateForall(t, y, x)
      }
      thenHave(exists(y, in(pair(t, y), p2) /\ in(pair(y, x), p2)) |- in(pair(t, x), p2)) by LeftExists

      have(thesis) by LeftOr(lastStep, predCase)
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }
  show

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
}
