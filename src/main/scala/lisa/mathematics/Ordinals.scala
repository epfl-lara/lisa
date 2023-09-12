package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.settheory.SetTheory.*
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
  val inductiveIntersectionExistence = Theorem(
    ∃(z, ∀(t, in(t, z) <=> ∀(y, inductive(y) ==> in(t, y))))
  ) {
    val inductExt =
      have(∃(x, inductive(x)) |- ∃(z, ∀(t, in(t, z) <=> ∀(y, inductive(y) ==> in(t, y))))) by InstPredSchema(Map(P -> lambda(x, inductive(x))))(intersectionOfPredicateClassExists)
    have(∃(z, ∀(t, in(t, z) <=> ∀(y, inductive(y) ==> in(t, y))))) by Cut(inductiveSetExists, inductExt)
  }

  /**
   * Theorem --- The intersection of all inductive sets is unique
   */
  val inductiveIntersectionUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> ∀(y, inductive(y) ==> in(t, y))))
  ) {
    val prop = ∀(y, inductive(y) ==> in(t, y))
    val fprop = ∀(t, in(t, z) <=> prop)

    val existsRhs = have(∃(z, fprop) |- ∃!(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniqueByExtension)
    val existsLhs = have(∃(z, fprop)) by Restate.from(inductiveIntersectionExistence)

    have(∃!(z, fprop)) by Cut(existsLhs, existsRhs)
  }

  /**
   * Natural Numbers (Inductive definition) --- The intersection of all
   * inductive sets is the set of natural numbers, N.
   */
  val naturalsInductive = DEF() --> The(z, ∀(t, in(t, z) <=> (∀(y, inductive(y) ==> in(t, y)))))(inductiveIntersectionUniqueness)

  /**
   * Theorem --- Natural numbers form an inductive set
   */
  val naturalsAreInductive = Theorem(
    inductive(naturalsInductive())
  ) {
    val defHypo = have(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- ∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x))))) by Hypothesis

    // emptySet is in N
    have(inductive(x) ==> in(∅, x)) by Weakening(inductive.definition)
    val inductEmpty = thenHave(∀(x, inductive(x) ==> in(∅, x))) by RightForall

    val defEmpty =
      have(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- (in(∅, z) <=> (∀(x, inductive(x) ==> in(∅, x))))) by InstantiateForall(∅)(defHypo)

    have(
      ∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- (in(∅, z) <=> (∀(x, inductive(x) ==> in(∅, x)))) /\ ∀(x, inductive(x) ==> in(∅, x))
    ) by RightAnd(defEmpty, inductEmpty)
    val baseCase = thenHave(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- in(∅, z)) by Tautology

    // if y in N, then succ y in N
    have(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- (in(t, z) <=> (∀(x, inductive(x) ==> in(t, x))))) by InstantiateForall(t)(defHypo)
    thenHave(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (in(t, z) <=> (∀(x, inductive(x) ==> in(t, x))))) by Weakening
    thenHave(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (∀(x, inductive(x) ==> in(t, x)))) by Tautology
    thenHave(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) /\ in(t, z) |- (inductive(x) ==> in(t, x))) by InstantiateForall(x)
    val inInductive = thenHave((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x)) by Restate

    have(inductive(x) |- ∀(t, in(t, x) ==> in(successor(t), x))) by Weakening(inductive.definition)
    val inInductiveDef = thenHave(inductive(x) |- in(t, x) ==> in(successor(t), x)) by InstantiateForall(t)

    have((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(t, x) /\ (in(t, x) ==> in(successor(t), x))) by RightAnd(inInductive, inInductiveDef)
    thenHave((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) /\ in(t, z), inductive(x)) |- in(successor(t), x)) by Tautology
    thenHave((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))), in(t, z)) |- inductive(x) ==> in(successor(t), x)) by Restate
    val succInst = thenHave((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))), in(t, z)) |- ∀(x, inductive(x) ==> in(successor(t), x))) by RightForall

    val nDefSucc =
      have(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- (in(successor(t), z) <=> (∀(x, inductive(x) ==> in(successor(t), x))))) by InstantiateForall(successor(t))(defHypo)
    have(
      (∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))), in(t, z)) |- ∀(x, inductive(x) ==> in(successor(t), x)) /\ (in(successor(t), z) <=> (∀(
        x,
        inductive(x) ==> in(successor(t), x)
      )))
    ) by RightAnd(succInst, nDefSucc)
    thenHave((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))), in(t, z)) |- in(successor(t), z)) by Tautology
    thenHave((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x))))) |- in(t, z) ==> in(successor(t), z)) by Restate
    val inductiveCase = thenHave(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- ∀(t, in(t, z) ==> in(successor(t), z))) by RightForall

    have(∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))) |- in(∅, z) /\ ∀(t, in(t, z) ==> in(successor(t), z))) by RightAnd(baseCase, inductiveCase)

    val form = formulaVariable
    val inductIff = thenHave(
      (∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x)))), inductive(z) <=> (in(∅, z) /\ ∀(y, in(y, z) ==> in(successor(y), z)))) |- inductive(z)
    ) by RightSubstIff(List((inductive(z), in(∅, z) /\ ∀(y, in(y, z) ==> in(successor(y), z)))), lambda(form, form))

    val inductDef = have(inductive(z) <=> (in(∅, z) /\ ∀(y, in(y, z) ==> in(successor(y), z)))) by InstFunSchema(Map(x -> z))(inductive.definition)

    have((∀(t, in(t, z) <=> (∀(x, inductive(x) ==> in(t, x))))) |- inductive(z)) by Cut(inductDef, inductIff)
    val inductExpansion =
      thenHave((forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) |- inductive(naturalsInductive())) by InstFunSchema(Map(z -> naturalsInductive()))

    have((naturalsInductive() === naturalsInductive()) <=> forall(t, in(t, naturalsInductive()) <=> (forall(x, inductive(x) ==> in(t, x))))) by InstantiateForall(naturalsInductive())(
      naturalsInductive.definition
    )
    val natDef = thenHave(forall(t, in(t, naturalsInductive()) <=> forall(x, inductive(x) ==> in(t, x)))) by Restate

    have(inductive(naturalsInductive())) by Cut(natDef, inductExpansion)
  }

  private val A = variable

  /**
   * A set `'A` is transitive if and only if every member of `'A` is a subset of `'A`.
   * ∀ 'x. 'x∈ 'A ⟹ 'x ⊂ 'A
   */
  val transitiveSet = DEF(A) --> forall(x, in(x, A) ==> subset(x, A))

  /*
  private val R = predicate(2)
  /**
   * Show that the restriction of a functional to a set exists.
   */
  val predicateRestrictionExists = makeTHM(
     ∃!(r, forall(x,  forall(y, in(pair(x, y), r) <=> in(x, A) /\ in(y, A) /\ R(x, y))))
  ) {
    val z1 = firstInPair(z)
    val z2 = secondInPair(z)

    have ( ∃!(r, forall(z, in(z, r) <=> in(z, cartesianProduct(A, A)) /\ R(z1, z2)))) by UniqueComprehension(cartesianProduct(A, A), lambda(Seq(z, x), R(z1, z2)))
    showCurrentProof()

  }
   */

}
