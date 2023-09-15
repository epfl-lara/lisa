package lisa.mathematics
package settheory
package orderings

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.fol.Quantifiers.*
import lisa.mathematics.settheory.SetTheory.*
import lisa.mathematics.settheory.orderings.PartialOrders.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.prooflib.Substitution
import lisa.utils.FOLPrinter

object InclusionOrders extends lisa.Main {

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
        thenHave((in(y, x), b === y, c === x) |- in(b, c)) by Substitution.ApplyRules(b === y, c === x)
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
    val subs = thenHave(subset(inclusionOn(a), cartesianProduct(a, a))) by Substitution.ApplyRules(subsetAxiom of (x -> inclusionOn(a), y -> cartesianProduct(a, a)))

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
    thenHave(thesis) by Substitution.ApplyRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is an irreflexive relation.
   */
  val emptyInclusionIrreflexive = Lemma(
    () |- irreflexive(inclusionOn(emptySet()), a)
  ) {
    have(irreflexive(emptySet(), a)) by Restate.from(emptyRelationIrreflexive)
    thenHave(thesis) by Substitution.ApplyRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is a transitive relation.
   */
  val emptyInclusionTransitive = Lemma(
    () |- transitive(inclusionOn(emptySet()), a)
  ) {
    have(transitive(emptySet(), a)) by Restate.from(emptyRelationTransitive)
    thenHave(thesis) by Substitution.ApplyRules(emptySetInclusionEmpty)
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
    ) by Substitution.ApplyRules(firstInPairReduction, secondInPairReduction)(
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
    have(totalOrder(pair(emptySet(), emptySet())) <=> (partialOrder(pair(emptySet(), emptySet())) /\ total(emptySet(), emptySet()))) by Substitution.ApplyRules(
      firstInPairReduction of (x -> emptySet(), y -> emptySet()),
      secondInPairReduction of (x -> emptySet(), y -> emptySet())
    )(totalOrder.definition of p -> pair(emptySet(), emptySet()))
    have(thesis) by Tautology.from(lastStep, emptySetPartialOrder, emptyRelationTotalOnItself)
  }
}
