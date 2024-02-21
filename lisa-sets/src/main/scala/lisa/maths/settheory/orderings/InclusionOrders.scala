package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.automation.kernel.CommonTactics.*

import PartialOrders.*
import WellOrders.*

object InclusionOrders extends lisa.Main {

  draft()

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
  private val F = function[1]
  private val G = function[2]

  private val P = predicate[1]
  private val Q = predicate[1]
  private val schemPred = predicate[1]

  val inclusionOnUniqueness = Lemma(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, cartesianProduct(a, a)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))))
  ) {
    have(thesis) by UniqueComprehension(cartesianProduct(a, a), lambda(t, exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))
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
   * Theorem --- the inclusion order on any set is a relation.
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

  /**
    * Theorem --- the inclusion order on the any set is anti-reflexive.
    * 
    * `∀x ∈ a, (x, x) ∉ ∈_a`
    */
  val inclusionIsAntiReflexive = Theorem(
    antiReflexive(inclusionOn(a), a)
  ) {
    val rel = inclusionOn(a)

    val antiReflexivity = have(!in(pair(x, x), rel)) subproof {
      assume(in(pair(x, x), rel))
      val xx = have(in(x, x)) by Tautology.from(inclusionOrderElem of (a -> a, b -> x, c -> x))
      have(bot) by Tautology.from(xx, inclusionAntiReflexive of (x -> x))
      thenHave(thesis) by Restate
    }

    val quant = thenHave(forall(x, !in(pair(x, x), rel))) by RightForall
    have(thesis) by Tautology.from(quant, inclusionIsRelation, antiReflexive.definition of (r -> rel, x -> a))
  }

  /**
    * Theorem --- the inclusion order on any set is anti-symmetric.
    * 
    * `∀x, y ∈ a, (x, y) ∈ ∈_a ∧ (y, x) ∈ ∈_a ⇒ x = y`
    */
  val inclusionIsAntiSymmetric = Theorem(
    antiSymmetric(inclusionOn(a), a)
  ) {
    val rel = inclusionOn(a)

    val antiSymmetry = have((in(pair(y, z), rel), in(pair(z, y), rel)) |- (y === z)) subproof {
      assume(in(pair(y, z), rel), in(pair(z, y), rel))

      val yz = have(in(y, z)) by Tautology.from(inclusionOrderElem of (a -> a, b -> y, c -> z))
      val zy = have(in(z, y)) by Tautology.from(inclusionOrderElem of (a -> a, b -> z, c -> y))

      have(bot) by Tautology.from(yz, zy, inclusionAntiSymmetric of (x -> z))
      thenHave(thesis) by Weakening
    }
    
    thenHave((in(pair(y, z), rel) /\ in(pair(z, y), rel)) ==> (y === z)) by Weakening
    thenHave(forall(z, (in(pair(y, z), rel) /\ in(pair(z, y), rel)) ==> (y === z))) by RightForall
    val quant = thenHave(forall(y, forall(z, (in(pair(y, z), rel) /\ in(pair(z, y), rel)) ==> (y === z)))) by RightForall
    
    have(thesis) by Tautology.from(quant, inclusionIsRelation, antiSymmetric.definition of (r -> rel, x -> a))
  }

  /**
   * Theorem --- the inclusion order on the empty set is the empty relation.
   */
  val emptySetInclusionEmpty = Lemma(
    () |- (inclusionOn(emptySet) === emptySet)
  ) {
    have(forall(t, in(t, inclusionOn(emptySet)) <=> (in(t, cartesianProduct(emptySet, emptySet)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(
      inclusionOn(emptySet)
    )(inclusionOn.definition of (a -> emptySet))
    val incDef = thenHave(in(t, inclusionOn(emptySet)) <=> (in(t, cartesianProduct(emptySet, emptySet)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))) by InstantiateForall(t)

    have(forall(t, in(t, cartesianProduct(emptySet, emptySet)) <=> in(t, emptySet))) by Tautology.from(
      productWithEmptySetEmpty of (x -> emptySet),
      extensionalityAxiom of (x -> cartesianProduct(emptySet, emptySet), y -> emptySet)
    )
    val emp = thenHave(in(t, cartesianProduct(emptySet, emptySet)) <=> in(t, emptySet)) by InstantiateForall(t)

    val impl = have(in(t, inclusionOn(emptySet)) <=> in(t, emptySet)) subproof {
      val lhs = have(in(t, inclusionOn(emptySet)) |- in(t, emptySet)) by Tautology.from(incDef, emp)
      val rhs = have(in(t, emptySet) |- in(t, inclusionOn(emptySet))) by Weakening(emptySet.definition of (x -> t))
      have(thesis) by Tautology.from(lhs, rhs)
    }

    val ext = thenHave(forall(t, in(t, inclusionOn(emptySet)) <=> in(t, emptySet))) by RightForall
    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x -> inclusionOn(emptySet), y -> emptySet))
  }

  /**
   * Theorem --- the inclusion order on the empty set is a reflexive relation.
   */
  val emptyInclusionReflexive = Lemma(
    () |- reflexive(inclusionOn(emptySet), emptySet)
  ) {
    have(reflexive(emptySet, emptySet)) by Restate.from(emptyRelationReflexiveOnItself)
    thenHave(thesis) by Substitution.ApplyRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is an irreflexive relation.
   */
  val emptyInclusionIrreflexive = Lemma(
    () |- irreflexive(inclusionOn(emptySet), a)
  ) {
    have(irreflexive(emptySet, a)) by Restate.from(emptyRelationIrreflexive)
    thenHave(thesis) by Substitution.ApplyRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the inclusion order on the empty set is a transitive relation.
   */
  val emptyInclusionTransitive = Lemma(
    () |- transitive(inclusionOn(emptySet), a)
  ) {
    have(transitive(emptySet, a)) by Restate.from(emptyRelationTransitive)
    thenHave(thesis) by Substitution.ApplyRules(emptySetInclusionEmpty)
  }

  /**
   * Theorem --- the empty relation partially orders the empty set
   */
  val emptySetPartialOrder = Lemma(
    () |- partialOrder(pair(emptySet, emptySet))
  ) {
    have(
      partialOrder(pair(emptySet, emptySet)) <=> (relationBetween(emptySet, emptySet, emptySet) /\ antiSymmetric(emptySet, emptySet) /\ antiReflexive(
        emptySet,
        emptySet
      ) /\ transitive(emptySet, emptySet))
    ) by Substitution.ApplyRules(firstInPairReduction, secondInPairReduction)(
      partialOrder.definition of p -> pair(emptySet, emptySet)
    )
    have(thesis) by Tautology.from(
      lastStep,
      emptySetRelationOnItself,
      emptyRelationIrreflexive of a -> emptySet,
      emptyRelationTransitive of a -> emptySet,
      emptyRelationAntiSymmetric of a -> emptySet
    )
  }

  /**
   * Theorem --- the empty relation totally orders the empty set
   */
  val emptySetTotalOrder = Lemma(
    () |- totalOrder(pair(emptySet, emptySet))
  ) {
    have(totalOrder(pair(emptySet, emptySet)) <=> (partialOrder(pair(emptySet, emptySet)) /\ total(emptySet, emptySet))) by Substitution.ApplyRules(
      firstInPairReduction of (x -> emptySet, y -> emptySet),
      secondInPairReduction of (x -> emptySet, y -> emptySet)
    )(totalOrder.definition of p -> pair(emptySet, emptySet))
    have(thesis) by Tautology.from(lastStep, emptySetPartialOrder, emptyRelationTotalOnItself)
  }

  val lowerPairInInclusionOrderSubset = Lemma(
    (b ⊆ a, pair(x, y) ∈ inclusionOn(a), x ∈ b, y ∈ b) |- pair(x, y) ∈ inclusionOn(b)
  ) {
    assumeAll

    have(x ∈ y) by Tautology.from(inclusionOrderElem of (a -> a, b -> x, c -> y))
    thenHave(x ∈ y /\ x ∈ b /\ y ∈ b) by Tautology
    have(thesis) by Tautology.from(inclusionOrderElem of (a -> b, b -> x, c -> y), lastStep)
  }

  val liftPairInInclusionRelationSubset = Lemma(
    (b ⊆ a, pair(x, y) ∈ inclusionOn(b)) |- pair(x, y) ∈ inclusionOn(a)
  ) {
    assumeAll

    have(x ∈ y /\ x ∈ b /\ y ∈ b) by Tautology.from(inclusionOrderElem of (a -> b, b -> x, c -> y))
    have(x ∈ y /\ x ∈ a /\ y ∈ a) by Tautology.from(lastStep, elementOfSubset of (y -> b, z -> a), elementOfSubset of (x -> y, y-> b, z -> a))
    have(thesis) by Tautology.from(inclusionOrderElem of (a -> a, b -> x, c -> y), lastStep)
  }

  val inclusionOrderTransitivityHoldsForSubsets = Lemma(
    (b ⊆ a, transitive(inclusionOn(a), a)) |- transitive(inclusionOn(b), b)
  ) {
    assumeAll

    val ina = inclusionOn(a)
    val inb = inclusionOn(b)

    have(in(pair(x, y), inb) /\ in(pair(y, z), inb) |- in(pair(x, z), inb)) subproof {
      assumeAll

      val pairsInA = have(pair(x, y) ∈ ina /\ pair(y, z) ∈ ina) by Tautology.from(liftPairInInclusionRelationSubset, liftPairInInclusionRelationSubset of (x -> y, y -> z))

      val xzInB = have(x ∈ b /\ z ∈ b) by Tautology.from(inclusionOrderElem of (a -> b, b -> x, c -> y), inclusionOrderElem of (a -> b, b -> y, c -> z))

      // but we know ina is transitive
      have(transitive(ina, a)) by Restate

      have(forall(x, forall(y, forall(z, (in(pair(x, y), ina) /\ in(pair(y, z), ina)) ==> in(pair(x, z), ina))))) by Tautology.from(transitive.definition of (r -> ina, x -> a), lastStep)
      thenHave((in(pair(x, y), ina) /\ in(pair(y, z), ina)) ==> in(pair(x, z), ina)) by InstantiateForall(x, y, z)

      have(thesis) by Tautology.from(pairsInA, lastStep, xzInB, lowerPairInInclusionOrderSubset of y -> z)

    }

    thenHave((in(pair(x, y), inb) /\ in(pair(y, z), inb)) ==> in(pair(x, z), inb)) by Restate
    thenHave(forall(z, (in(pair(x, y), inb) /\ in(pair(y, z), inb)) ==> in(pair(x, z), inb))) by RightForall
    thenHave(forall(y, forall(z, (in(pair(x, y), inb) /\ in(pair(y, z), inb)) ==> in(pair(x, z), inb)))) by RightForall
    thenHave(forall(x, forall(y, forall(z, (in(pair(x, y), inb) /\ in(pair(y, z), inb)) ==> in(pair(x, z), inb))))) by RightForall
    have(thesis) by Tautology.from(lastStep, inclusionIsRelation of (a -> b), transitive.definition of (r -> inb, x -> b))
  }

  val inclusionOrderTotalityHoldsForSubsets = Lemma(
    (b ⊆ a, total(inclusionOn(a), a)) |- total(inclusionOn(b), b)
  ) {
    assumeAll

    val ina = inclusionOn(a)
    val inb = inclusionOn(b)

    have(x ∈ b /\ y ∈ b |- (pair(x, y) ∈ inb) \/ (pair(y, x) ∈ inb) \/ (x === y)) subproof {
      assumeAll

      val xyInA = have(x ∈ a /\ y ∈ a) by Tautology.from(elementOfSubset of (x -> x, y -> b, z -> a), elementOfSubset of (x -> y, y -> b, z -> a))

      // but we know ina is total
      have(total(ina, a)) by Restate

      have(forall(x, forall(y, (x ∈ a /\ y ∈ a) ==> (pair(x, y) ∈ ina \/ (pair(y, x) ∈ ina) \/ (x === y))))) by Tautology.from(total.definition of (r -> ina, x -> a), lastStep)
      thenHave((x ∈ a /\ y ∈ a) ==> (pair(x, y) ∈ ina \/ (pair(y, x) ∈ ina) \/ (x === y))) by InstantiateForall(x, y)

      have(thesis) by Tautology.from(lastStep, xyInA, lowerPairInInclusionOrderSubset, lowerPairInInclusionOrderSubset of (y -> x, x -> y))
    }

    thenHave((x ∈ b /\ y ∈ b) ==> (pair(x, y) ∈ inb) \/ (pair(y, x) ∈ inb) \/ (x === y)) by Restate
    thenHave(forall(y, (x ∈ b /\ y ∈ b) ==> (pair(x, y) ∈ inb) \/ (pair(y, x) ∈ inb) \/ (x === y))) by RightForall
    thenHave(forall(x, forall(y, (x ∈ b /\ y ∈ b) ==> (pair(x, y) ∈ inb) \/ (pair(y, x) ∈ inb) \/ (x === y)))) by RightForall
    have(thesis) by Tautology.from(lastStep, inclusionIsRelation of (a -> b), total.definition of (r -> inb, x -> b))
  }

  val inclusionPartialOrderOnSubset = Theorem(
    (partialOrder(inclusionOrderOn(a)), b ⊆ a) |- partialOrder(inclusionOrderOn(b))
  ) {
    assumeAll

    val orda = inclusionOrderOn(a)
    val ordb = inclusionOrderOn(b)
    val ina = inclusionOn(a)
    val inb = inclusionOn(b)

    val incDef = have(inclusionOrderOn(x) === pair(x, inclusionOn(x))) by Tautology.from(inclusionOrderOn.definition of (inclusionOrderOn(x), a -> x))

    // we get 2/3 properties for free with the inclusion order
    val antiSymmetry = have(antiSymmetric(ordb._2, ordb._1)) subproof {
      have(antiSymmetric(inb, b)) by Weakening(inclusionIsAntiSymmetric of (a -> b))
      thenHave(antiSymmetric(pair(b, inb)._2, pair(b, inb)._1)) by Substitution.ApplyRules(_1.definition of (x -> b, y -> inb), _2.definition of (x -> b, y -> inb))
      thenHave(thesis) by Substitution.ApplyRules(incDef of (x -> b))
    }
    val irreflexivity = have(irreflexive(ordb._2, ordb._1)) subproof {
      have(irreflexive(inb, b)) by Weakening(inclusionIsAntiReflexive of (a -> b))
      thenHave(irreflexive(pair(b, inb)._2, pair(b, inb)._1)) by Substitution.ApplyRules(_1.definition of (x -> b, y -> inb), _2.definition of (x -> b, y -> inb))
      thenHave(thesis) by Substitution.ApplyRules(incDef of (x -> b))
    }

    // we need to prove transitivity

    val transitivity = have(transitive(ordb._2, ordb._1)) subproof {
      // we know ina is transitive
      have(transitive(ina, a)) subproof {
        have(transitive(orda._2, orda._1)) by Tautology.from(partialOrder.definition of (p -> orda))
        thenHave(transitive(pair(a, ina)._2, pair(a, ina)._1)) by Substitution.ApplyRules(incDef of (x -> a))
        thenHave(transitive(ina, a)) by Substitution.ApplyRules(_1.definition of (x -> a, y -> ina), _2.definition of (x -> a, y -> ina))
      }
      // so inb must be too
      have(transitive(inb, b)) by Tautology.from(inclusionOrderTransitivityHoldsForSubsets, lastStep)

      thenHave(transitive(pair(b, inb)._2, pair(b, inb)._1)) by Substitution.ApplyRules(_1.definition of (x -> b, y -> inb), _2.definition of (x -> b, y -> inb))
      thenHave(thesis) by Substitution.ApplyRules(incDef of (x -> b))
    }

    val relational = have(relationBetween(ordb._2, ordb._1, ordb._1)) subproof {
      have(relationBetween(inb, b, b)) by Weakening(inclusionIsRelation of (a -> b))
      thenHave(relationBetween(pair(b, inb)._2, pair(b, inb)._1, pair(b, inb)._1)) by Substitution.ApplyRules(_1.definition of (x -> b, y -> inb), _2.definition of (x -> b, y -> inb))
      thenHave(thesis) by Substitution.ApplyRules(incDef of (x -> b))
    }

    have(thesis) by Tautology.from(antiSymmetry, irreflexivity, transitivity, relational, partialOrder.definition of (p -> ordb))
  }

  val inclusionTotalOrderOnSubset = Theorem(
    (totalOrder(inclusionOrderOn(a)), b ⊆ a) |- totalOrder(inclusionOrderOn(b))
  ) {
    assumeAll

    val orda = inclusionOrderOn(a)
    val ordb = inclusionOrderOn(b)

    val ina = inclusionOn(a)
    val inb = inclusionOn(b)

    val incDef = have(inclusionOrderOn(x) === pair(x, inclusionOn(x))) by Tautology.from(inclusionOrderOn.definition of (inclusionOrderOn(x), a -> x))

    val partialOrdering = have(partialOrder(ordb)) by Tautology.from(inclusionPartialOrderOnSubset of (a -> a, b -> b), totalOrder.definition of (p -> orda))
    
    val totality = have(total(ordb._2, ordb._1)) subproof {
      // we know ina is total
      have(total(ina, a)) subproof {
        have(total(orda._2, orda._1)) by Tautology.from(totalOrder.definition of (p -> orda))
        thenHave(total(pair(a, ina)._2, pair(a, ina)._1)) by Substitution.ApplyRules(incDef of (x -> a))
        thenHave(total(ina, a)) by Substitution.ApplyRules(_1.definition of (x -> a, y -> ina), _2.definition of (x -> a, y -> ina))
      }

      // so inb is total
      have(total(inb, b)) by Tautology.from(inclusionOrderTotalityHoldsForSubsets, lastStep)
      thenHave(total(pair(b, inb)._2, pair(b, inb)._1)) by Substitution.ApplyRules(_1.definition of (x -> b, y -> inb), _2.definition of (x -> b, y -> inb))
      thenHave(total(ordb._2, ordb._1)) by Substitution.ApplyRules(incDef of (x -> b))

    }

    have(thesis) by Tautology.from(partialOrdering, totality, totalOrder.definition of (p -> ordb))
  }

  val inclusionWellOrderOnSubset = Theorem(
    (wellOrder(inclusionOrderOn(a)), b ⊆ a) |- wellOrder(inclusionOrderOn(b))
  ) {
    assumeAll

    val orda = inclusionOrderOn(a)
    val ordb = inclusionOrderOn(b)

    val ina = inclusionOn(a)
    val inb = inclusionOn(b)

    val incDef = have(inclusionOrderOn(x) === pair(x, inclusionOn(x))) by Tautology.from(inclusionOrderOn.definition of (inclusionOrderOn(x), a -> x))

    val totalOrdering = have(totalOrder(ordb)) by Tautology.from(inclusionTotalOrderOnSubset, wellOrder.definition of (p -> orda))

    val minElems = have(c ⊆ b /\ !(c === ∅) |- exists(z, z ∈ c /\ forall(y, y ∈ c ==> pair(z, y) ∈ inb \/ (z === y)))) subproof {
      assumeAll

      have(forall(c, (c ⊆ orda._1 /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ orda._2 \/ (z === y)))))) by Tautology.from(wellOrder.definition of (p -> orda))
      thenHave(forall(c, (c ⊆ pair(a, ina)._1 /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ pair(a, ina)._2 \/ (z === y)))))) by Substitution.ApplyRules(incDef of (x -> a))
      thenHave(forall(c, (c ⊆ a /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y)))))) by Substitution.ApplyRules(_1.definition of (x -> a, y -> ina), _2.definition of (x -> a, y -> ina))
      thenHave((c ⊆ a /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y))))) by InstantiateForall(c)
      val exz = have(exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y))))) by Tautology.from(lastStep, subsetTransitivity of (a -> c, b -> b, c -> a))

      // reduce (z, y) ∈ ina to (z, y) ∈ inb under quantifiers
      have((z ∈ c, y ∈ c, pair(z, y) ∈ ina \/ (z === y)) |- (pair(z, y) ∈ inb) \/ (z === y)) subproof {
        assumeAll
        have(z ∈ b /\ y ∈ b) by Tautology.from(elementOfSubset of (x -> z, y -> c, z -> b), elementOfSubset of (x -> y, y -> c, z -> b))
        have(thesis) by Tautology.from(lowerPairInInclusionOrderSubset of (x -> z), lastStep)
      }

      // quantifiers >:)
      thenHave((z ∈ c, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y))) |- y ∈ c ==> (pair(z, y) ∈ inb \/ (z === y))) by Tautology
      thenHave((z ∈ c, forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y)))) |- y ∈ c ==> (pair(z, y) ∈ inb \/ (z === y))) by LeftForall
      thenHave((z ∈ c, forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y)))) |- forall(y, y ∈ c ==> (pair(z, y) ∈ inb \/ (z === y)))) by RightForall
      thenHave(z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y))) |- z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ inb \/ (z === y)))) by Tautology
      thenHave(z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y))) |- exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ inb \/ (z === y))))) by RightExists
      thenHave(exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ ina \/ (z === y)))) |- exists(z, z ∈ c /\ forall(y, y ∈ c ==> (pair(z, y) ∈ inb \/ (z === y))))) by LeftExists

      have(thesis) by Tautology.from(exz, lastStep)
    }

    have(wellOrder(ordb)) subproof {
      have((c ⊆ b /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> pair(z, y) ∈ inb \/ (z === y)))) by Restate.from(minElems)
      thenHave(forall(c, (c ⊆ b /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> pair(z, y) ∈ inb \/ (z === y))))) by RightForall
      thenHave(forall(c, (c ⊆ pair(b, inb)._1 /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> pair(z, y) ∈ pair(b, inb)._2 \/ (z === y))))) by Substitution.ApplyRules(_1.definition of (x -> b, y -> inb), _2.definition of (x -> b, y -> inb))
      thenHave(forall(c, (c ⊆ ordb._1 /\ !(c === ∅)) ==> exists(z, z ∈ c /\ forall(y, y ∈ c ==> pair(z, y) ∈ ordb._2 \/ (z === y))))) by Substitution.ApplyRules(incDef of (x -> b))

      have(thesis) by Tautology.from(lastStep, totalOrdering, wellOrder.definition of (p -> ordb))
    }
  }
}
