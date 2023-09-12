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
import lisa.mathematics.settheory.orderings.WellOrders.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.prooflib.Substitution
import lisa.utils.FOLPrinter

object Ordinals extends lisa.Main {

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
    thenHave(thesis) by Substitution.ApplyRules(transitiveSet.definition)
  }

  /**
   * Theorem --- the empty set is well ordered by inclusion.
   */
  val emptySetWellOrderedByInclusion = Lemma(
    () |- wellOrder(inclusionOrderOn(emptySet()))
  ) {
    val incDef = have(inclusionOrderOn(emptySet()) === pair(emptySet(), inclusionOn(emptySet()))) by InstantiateForall(inclusionOrderOn(emptySet()))(inclusionOrderOn.definition of a -> emptySet())
    have(wellOrder(pair(emptySet(), inclusionOn(emptySet())))) by Substitution.ApplyRules(emptySetInclusionEmpty)(emptySetWellOrder)
    thenHave(thesis) by Substitution.ApplyRules(incDef)
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
    val wellOrda = have(ordinal(a) |- wellOrder(pair(a, inclusionOn(a)))) by Substitution.ApplyRules(lastStep)(wellOrdInca)

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
        .ApplyRules(secondInPairReduction of (x -> a, y -> inclusionOn(a)))(wellOrderTransitivity of p -> pair(a, inclusionOn(a)))
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
    thenHave((transitiveSet(a), wellOrder(pair(a, inclusionOn(a))), in(b, a)) |- transitiveSet(b)) by Substitution.ApplyRules(transitiveSetInclusionDef of x -> b)
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
          thenHave(total(secondInPair(pair(a, inclusionOn(a))), firstInPair(pair(a, inclusionOn(a))))) by Substitution.ApplyRules(incEq)
          val totIncA =
            thenHave(total(inclusionOn(a), a)) by Substitution.ApplyRules(secondInPairReduction of (x -> a, y -> inclusionOn(a)), firstInPairReduction of (x -> a, y -> inclusionOn(a)))

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
        val snd = thenHave(secondInPair(inclusionOrderOn(b)) === inclusionOn(b)) by Substitution.ApplyRules(incEq)
        have(firstInPair(pair(b, inclusionOn(b))) === (b)) by Weakening(firstInPairReduction of (x -> b, y -> inclusionOn(b)))
        val fst = thenHave(firstInPair(inclusionOrderOn(b)) === (b)) by Substitution.ApplyRules(incEq)

        have(thesis) by Substitution.ApplyRules(snd, fst)(totB)
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
      ) by Substitution.ApplyRules(incDef)
      thenHave(forall(c, (subset(c, a) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), inclusionOn(a)) \/ (z === y)))))) by Substitution.ApplyRules(
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
      ) by Substitution.ApplyRules(firstInPairReduction of (x -> b, y -> inclusionOn(b)), secondInPairReduction of (x -> b, y -> inclusionOn(b)))(woProp)
      thenHave(
        forall(
          c,
          (subset(c, firstInPair(inclusionOrderOn(b))) /\ !(c === emptySet())) ==> exists(z, in(z, c) /\ forall(y, in(y, c) ==> (in(pair(z, y), secondInPair(inclusionOrderOn(b))) \/ (z === y))))
        )
      ) by Substitution.ApplyRules(incDef)
      have(thesis) by Tautology.from(lastStep, totalB, wellOrder.definition of p -> inclusionOrderOn(b))
    }

    have(thesis) by Tautology.from(wo, transitiveB, ordinal.definition of (a -> b))
  }

  val ordinalSubclassHasMinimalElement = Lemma(
    forall(x, P(x) ==> ordinal(x)) /\ exists(x, P(x)) |- exists(y, P(y) /\ ordinal(y) /\ forall(x, P(x) ==> in(y, x)))
  ) {
    sorry
  }
}
