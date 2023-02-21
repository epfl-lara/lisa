package lisa.mathematics

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*

/**
 * Implements theorems about first-order logic.
 */
object FirstOrderLogic extends lisa.Main {

  private val x = variable
  private val y = variable
  private val z = variable
  private val a = variable
  private val b = variable
  private val c = variable
  private val p = formulaVariable
  private val P = predicate(1)
  private val Q = predicate(1)

  /**
   * Theorem --- A formula is equivalent to itself universally quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaUniversal = Theorem(
    () |- ∀(x, p()) <=> p()
  ) {
    val base = have(p() |- p()) by Hypothesis

    have(p() |- ∀(x, p())) by RightForall(base)
    val lhs = thenHave(() |- p() ==> ∀(x, p())) by Restate

    have(∀(x, p()) |- p()) by LeftForall(base)
    val rhs = thenHave(() |- ∀(x, p()) ==> p()) by Restate

    have(thesis) by RightIff(lhs, rhs)
  }

  /**
   * Theorem --- A formula is equivalent to itself existentially quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaExistential = Theorem(
    () |- ∃(x, p()) <=> p()
  ) {
    val base = have(p() |- p()) by Hypothesis

    have(p() |- ∃(x, p())) by RightExists(base)
    val lhs = thenHave(() |- p() ==> ∃(x, p())) by Restate

    have(∃(x, p()) |- p()) by LeftExists(base)
    val rhs = thenHave(() |- ∃(x, p()) ==> p()) by Restate

    have(thesis) by RightIff(lhs, rhs)
  }

  /**
    * Theorem --- If there exists a *unique* element satisfying a predicate,
    * then we can say there *exists* an element satisfying it as well.
    */
  val existsOneImpliesExists = Theorem(
    ∃!(x, P(x)) |- ∃(x, P(x))
  ) {
    have((x === y) <=> P(y) |- (x === y) <=> P(y)) by Hypothesis
    thenHave(∀(y, (x === y) <=> P(y)) |- (x === y) <=> P(y)) by LeftForall
    thenHave(∀(y, (x === y) <=> P(y)) |- P(x)) by InstFunSchema(Map(y -> x))
    thenHave(∀(y, (x === y) <=> P(y)) |- ∃(x, P(x))) by RightExists
    thenHave(∃(x, ∀(y, (x === y) <=> P(y))) |- ∃(x, P(x))) by LeftExists
    thenHave(thesis) by Restate
  }

  /**
    * Theorem --- Equality relation is transitive
    */
  val equalityTransitivity = Theorem(
    (x === y) /\ (y === z) |- (x === z)
  ) {
    have((x === y) |- (x === y)) by Hypothesis
    thenHave(((x === y), (y === z)) |- (x === z)) by RightSubstEq.apply2
    thenHave(thesis) by Restate
  }

  /**
    * Theorem --- Conjunction and universal quantification commute
    */
  val universalConjunctionCommutation = Theorem(
    () |- forall(x, P(x) /\ Q(x)) <=> forall(x, P(x)) /\ forall(x, Q(x))
  ) {
    // forward direction
    val fwd = have(forall(x, P(x) /\ Q(x)) ==> forall(x, P(x)) /\ forall(x, Q(x))) subproof {
      have(P(x) /\ Q(x) |- P(x)) by Restate
      thenHave(forall(x, P(x) /\ Q(x)) |- P(x)) by LeftForall
      val px = thenHave(forall(x, P(x) /\ Q(x)) |- forall(x, P(x))) by RightForall

      have(P(x) /\ Q(x) |- Q(x)) by Restate
      thenHave(forall(x, P(x) /\ Q(x)) |- Q(x)) by LeftForall
      val qx = thenHave(forall(x, P(x) /\ Q(x)) |- forall(x, Q(x))) by RightForall

      have(forall(x, P(x) /\ Q(x)) |- forall(x, P(x)) /\ forall(x, Q(x))) by RightAnd(px, qx)
      thenHave(thesis) by Restate
    }

    // backward direction
    val bwd = have(forall(x, P(x)) /\ forall(x, Q(x)) ==> forall(x, P(x) /\ Q(x))) subproof {
      have((P(x), Q(x)) |- P(x) /\ Q(x)) by Restate
      thenHave((forall(x, P(x)), Q(x)) |- P(x) /\ Q(x)) by LeftForall
      thenHave((forall(x, P(x)), forall(x, Q(x))) |- P(x) /\ Q(x)) by LeftForall
      thenHave((forall(x, P(x)), forall(x, Q(x))) |- forall(x, P(x) /\ Q(x))) by RightForall

      thenHave(thesis) by Restate
    }

    have(thesis) by RightIff(fwd, bwd)
  }

  /**
    * Theorem --- Disjunction and exisential quantification commute
    */
  val existentialDisjunctionCommutation = Theorem(
    () |- exists(x, P(x) \/ Q(x)) <=> exists(x, P(x)) \/ exists(x, Q(x))
  ) {
    // forward direction
    val fwd = have(exists(x, P(x) \/ Q(x)) ==> exists(x, P(x)) \/ exists(x, Q(x))) subproof {
      have(P(x) \/ Q(x) |- (P(x), Q(x))) by Restate
      thenHave(P(x) \/ Q(x) |- (exists(x, P(x)), Q(x))) by RightExists
      thenHave(P(x) \/ Q(x) |- (exists(x, P(x)), exists(x, Q(x)))) by RightExists
      thenHave(exists(x, P(x) \/ Q(x)) |- (exists(x, P(x)), exists(x, Q(x)))) by LeftExists

      thenHave(thesis) by Restate
    }

    // backward direction
    val bwd = have(exists(x, P(x)) \/ exists(x, Q(x)) ==> exists(x, P(x) \/ Q(x))) subproof {
      have(P(x) |- P(x) \/ Q(x)) by Restate
      thenHave(P(x) |- exists(x, P(x) \/ Q(x))) by RightExists
      val px = thenHave(exists(x, P(x)) |- exists(x, P(x) \/ Q(x))) by LeftExists

      have(Q(x) |- P(x) \/ Q(x)) by Restate
      thenHave(Q(x) |- exists(x, P(x) \/ Q(x))) by RightExists
      val qx = thenHave(exists(x, Q(x)) |- exists(x, P(x) \/ Q(x))) by LeftExists

      have(exists(x, P(x)) \/ exists(x, Q(x)) |- exists(x, P(x) \/ Q(x))) by LeftOr(px, qx)
      thenHave(thesis) by Restate
    }

    have(thesis) by RightIff(fwd, bwd)
  }

}
