package lisa.mathematics
package settheory
package orderings

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.fol.Quantifiers.*
import lisa.mathematics.settheory.SetTheory.*
import lisa.mathematics.settheory.orderings.InclusionOrders.*
import lisa.mathematics.settheory.orderings.Ordinals.*
import lisa.mathematics.settheory.orderings.PartialOrders.*
import lisa.mathematics.settheory.orderings.WellOrders.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.utils.FOLPrinter

object Segments extends lisa.Main {

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

  val initialSegmentElement = Lemma(
    partialOrder(p) |- in(pair(x, y), secondInPair(p)) <=> in(x, initialSegment(p, y))
  ) {
    assume(partialOrder(p))

    val p1 = firstInPair(p)
    val p2 = secondInPair(p)

    val fwd = have(in(pair(x, y), p2) |- in(x, initialSegment(p, y))) subproof {
      assume(in(pair(x, y), p2))

      // p2 is a relation on p1
      have(relationBetween(p2, p1, p1)) by Tautology.from(partialOrder.definition)
      val xInp1 = have(in(x, p1)) by Tautology.from(lastStep, pairInRelation of (r -> p2, a -> p1, b -> p1))
      have(forall(x, in(x, initialSegment(p, y)) <=> (in(x, p1) /\ in(pair(x, y), p2)))) by InstantiateForall(initialSegment(p, y))(initialSegment.definition of a -> y)
      thenHave(in(x, initialSegment(p, y)) <=> (in(x, p1) /\ in(pair(x, y), p2))) by InstantiateForall(x)

      have(thesis) by Tautology.from(xInp1, lastStep)
    }

    val bwd = have(in(x, initialSegment(p, y)) |- in(pair(x, y), p2)) subproof {
      have(forall(x, in(x, initialSegment(p, y)) <=> (in(x, p1) /\ in(pair(x, y), p2)))) by InstantiateForall(initialSegment(p, y))(initialSegment.definition of a -> y)
      thenHave(in(x, initialSegment(p, y)) <=> (in(x, p1) /\ in(pair(x, y), p2))) by InstantiateForall(x)
      thenHave(thesis) by Tautology
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

  val initialSegmentBaseElement = Lemma(
    partialOrder(p) /\ in(x, initialSegment(p, y)) |- in(x, firstInPair(p))
  ) {
    assume(partialOrder(p))
    assume(in(x, initialSegment(p, y)))

    val p1 = firstInPair(p)
    val p2 = secondInPair(p)

    val pairInp2 = have(in(pair(x, y), p2)) by Tautology.from(initialSegmentElement)
    have(relationBetween(p2, p1, p1)) by Tautology.from(partialOrder.definition)
    have(in(x, p1)) by Tautology.from(lastStep, pairInp2, pairInRelation of (r -> p2, a -> p1, b -> p1))
  }

  val initialSegmentIrreflexivity = Lemma(
    partialOrder(p) |- !in(x, initialSegment(p, x))
  ) {
    sorry
  }

  val predecessorInInitialSegment = Lemma(
    totalOrder(p) /\ predecessor(p, y, x) |- in(y, initialSegment(p, x))
  ) {
    assume(totalOrder(p))
    assume(predecessor(p, y, x))

    have(in(pair(y, x), secondInPair(p))) by Tautology.from(predecessor.definition of (x -> y, y -> x))
    have(in(y, initialSegment(p, x))) by Tautology.from(lastStep, totalOrder.definition, initialSegmentElement of (x -> y, y -> x))
  }

  val initialSegmentsSubset = Lemma(
    partialOrder(p) /\ in(pair(x, y), secondInPair(p)) |- subset(initialSegment(p, x), initialSegment(p, y))
  ) {
    // t \in <x iff t \in p1 and (t, x) \in p2

    // but we know (x, y) \in p2, so by transitivity, (t, y) \in p2

    // t \in p1 /\ (t, y) in p2 ==> t \in <y

    // <x \subseteq <y

    sorry
  }

  val initialSegmentTransitivity = Lemma(
    partialOrder(p) /\ in(x, initialSegment(p, y)) /\ in(y, initialSegment(p, z)) |- in(x, initialSegment(p, z))
  ) {
    assume(partialOrder(p))
    assume(in(x, initialSegment(p, y)))
    assume(in(y, initialSegment(p, z)))

    val xy = have(in(pair(x, y), secondInPair(p))) by Tautology.from(initialSegmentElement of (x -> x, y -> y))
    val yz = have(in(pair(y, z), secondInPair(p))) by Tautology.from(initialSegmentElement of (x -> y, y -> z))

    have(forall(x, forall(y, forall(z, (in(pair(x, y), secondInPair(p)) /\ in(pair(y, z), secondInPair(p))) ==> in(pair(x, z), secondInPair(p)))))) by Tautology.from(
      partialOrder.definition,
      transitive.definition of (r -> secondInPair(p), x -> firstInPair(p))
    )
    thenHave((in(pair(x, y), secondInPair(p)) /\ in(pair(y, z), secondInPair(p))) ==> in(pair(x, z), secondInPair(p))) by InstantiateForall(x, y, z)
    have(in(pair(x, z), secondInPair(p))) by Tautology.from(lastStep, xy, yz)

    have(thesis) by Tautology.from(lastStep, initialSegmentElement of (x -> x, y -> z))
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

  val initialSegmentPredecessorSplit = Lemma(
    totalOrder(p) /\ predecessor(p, y, x) |- in(z, initialSegment(p, x)) <=> ((z === y) \/ in(z, initialSegment(p, y)))
  ) {
    sorry
  }

  val initialSegmentIntersection = Lemma(
    partialOrder(p) /\ in(y, initialSegment(p, x)) |- setIntersection(initialSegment(p, y), initialSegment(p, x)) === initialSegment(p, y)
  ) {
    sorry
  }

  /**
   * The restriction of a function `f` with respect to `a` relative to a
   * partial order `p = (X, <)`. The result is `f` with its domain restricted
   * to the elements less than `a` wrt `<`.
   */
  val orderedRestriction = DEF(f, a, p) --> restrictedFunction(f, initialSegment(p, a))

  /**
   * Theorem --- Ordered Restriction Membership
   *
   * A pair `b` is in the ordered restriction of a function `f` to the initial
   * segment of `a` under a partial order `p` iff it is in `f` and its first element
   * (the one in the domain) is in the initial segment of `a`
   */
  val orderedRestrictionMembership = Lemma(
    partialOrder(p) |- in(b, orderedRestriction(f, a, p)) <=> (in(b, f) /\ in(firstInPair(b), initialSegment(p, a)))
  ) {
    sorry
  }

  val orderedRestrictionFunctionalOverInit = Lemma(
    in(a, initialSegment(p, b)) /\ functionalOver(f, initialSegment(p, b)) |- functionalOver(orderedRestriction(f, a, p), initialSegment(p, a))
  ) {
    sorry
  }

  val orderedRestrictionAgreement = Lemma(
    partialOrder(p) /\ in(b, initialSegment(p, a)) /\ in(b, relationDomain(f)) /\ in(b, relationDomain(g)) |- (app(orderedRestriction(f, a, p), b) === app(orderedRestriction(g, a, p), b)) <=> (app(
      f,
      b
    ) === app(g, b))
  ) {
    sorry
  }

}
