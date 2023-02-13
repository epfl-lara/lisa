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

  private val P = predicate(1)
  private val Q = predicate(1)
  private val schemPred = predicate(1)

  /**
   * Chapter 2
   * Ordinal Numbers
   */

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

  /**
   * Theorem --- The intersection of all inductive sets is unique
   */
  val inductiveIntersectionUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> forall(y, inductive(y) ==> in(t, y))))
  ) {
    val prop = forall(y, inductive(y) ==> in(t, y))
    val fprop = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop) |- existsOne(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniqueByExtension)
    val existsLhs = have(() |- exists(z, fprop)) by Rewrite(inductiveIntersectionExistence)

    have(() |- existsOne(z, fprop)) by Cut(existsLhs, existsRhs)
  }

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
    val inductEmpty = thenHave(() |- forall(x, inductive(x) ==> in(emptySet(), x))) by RightForall

    val defEmpty =
      have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(emptySet(), z) <=> (forall(x, inductive(x) ==> in(emptySet(), x))))) by InstantiateForall(emptySet())(defHypo)

    have(
      forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(emptySet(), z) <=> (forall(x, inductive(x) ==> in(emptySet(), x)))) /\ forall(x, inductive(x) ==> in(emptySet(), x))
    ) by RightAnd(defEmpty, inductEmpty)
    val baseCase = thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- in(emptySet(), z)) by Tautology

    // if y in N, then succ y in N
    have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) by InstantiateForall(t)(defHypo)
    thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) by Weakening
    thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (forall(x, inductive(x) ==> in(t, x)))) by Tautology
    thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (inductive(x) ==> in(t, x))) by InstantiateForall(x)
    val inInductive = thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x)) by Restate

    have(inductive(x) |- forall(t, in(t, x) ==> in(successor(t), x))) by Weakening(inductive.definition)
    val inInductiveDef = thenHave(inductive(x) |- in(t, x) ==> in(successor(t), x)) by InstantiateForall(t)

    have(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x) /\ (in(t, x) ==> in(successor(t), x))) by RightAnd(inInductive, inInductiveDef)
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(successor(t), x)) by Tautology
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- inductive(x) ==> in(successor(t), x)) by Restate
    val succInst = thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- forall(x, inductive(x) ==> in(successor(t), x))) by RightForall

    val nDefSucc =
      have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- (in(successor(t), z) <=> (forall(x, inductive(x) ==> in(successor(t), x))))) by InstantiateForall(successor(t))(defHypo)
    have(
      Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- forall(x, inductive(x) ==> in(successor(t), x)) /\ (in(successor(t), z) <=> (forall(
        x,
        inductive(x) ==> in(successor(t), x)
      )))
    ) by RightAnd(succInst, nDefSucc)
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), in(t, z)) |- in(successor(t), z)) by Tautology
    thenHave(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) |- in(t, z) ==> in(successor(t), z)) by Restate
    val inductiveCase = thenHave(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- forall(t, in(t, z) ==> in(successor(t), z))) by RightForall

    have(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))) |- in(emptySet(), z) /\ forall(t, in(t, z) ==> in(successor(t), z))) by RightAnd(baseCase, inductiveCase)

    val form = formulaVariable
    val inductIff = thenHave(
      Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x)))), inductive(z) <=> (in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))) |- inductive(z)
    ) by RightSubstIff(List((inductive(z), in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))), lambda(form, form))

    val inductDef = have(() |- inductive(z) <=> (in(emptySet(), z) /\ forall(y, in(y, z) ==> in(successor(y), z)))) by InstFunSchema(Map(x -> z))(inductive.definition)

    have(Set(forall(t, in(t, z) <=> (forall(x, inductive(x) ==> in(t, x))))) |- inductive(z)) by Cut(inductDef, inductIff)
    val inductExpansion =
      thenHave(Set(forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) |- inductive(naturalsInductive())) by InstFunSchema(Map(z -> naturalsInductive()))

    have(() |- (naturalsInductive() === naturalsInductive()) <=> forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) by InstantiateForall(naturalsInductive())(
      naturalsInductive.definition
    )
    val natDef = thenHave(() |- forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) by Rewrite

    have(() |- inductive(naturalsInductive())) by Cut(natDef, inductExpansion)
  }
}
