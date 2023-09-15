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
import lisa.mathematics.settheory.orderings.PartialOrders.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.prooflib.Substitution
import lisa.utils.FOLPrinter

object WellOrders extends lisa.Main {

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
    ) by Substitution.ApplyRules(firstInPairReduction of (x -> emptySet(), y -> emptySet()))(wellOrder.definition of p -> pair(emptySet(), emptySet()))

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
        thenHave((forall(y, in(y, x) ==> subset(y, x)), in(y, x)) |- forall(z, in(z, y) ==> in(z, x))) by Substitution.ApplyRules(subsetAxiom of (x -> y, y -> x))
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
        thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- subset(y, x)) by Substitution.ApplyRules(subsetAxiom of (x -> y, y -> x))
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
}
