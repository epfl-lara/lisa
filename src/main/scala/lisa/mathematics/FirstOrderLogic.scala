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

  /**
   * Theorem --- A formula is equivalent to itself universally quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaUniversal = Theorem(
    () |- forall(x, p()) <=> p()
  ) {
    val base = have(p() |- p()) by Hypothesis

    have(p() |- forall(x, p())) by RightForall(base)
    val lhs = thenHave(() |- p() ==> forall(x, p())) by Restate

    have(forall(x, p()) |- p()) by LeftForall(base)
    val rhs = thenHave(() |- forall(x, p()) ==> p()) by Restate

    have(thesis) by RightIff(lhs, rhs)
  }

  /**
   * Theorem --- A formula is equivalent to itself existentially quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaExistential = Theorem(
    () |- exists(x, p()) <=> p()
  ) {
    val base = have(p() |- p()) by Hypothesis

    have(p() |- exists(x, p())) by RightExists(base)
    val lhs = thenHave(() |- p() ==> exists(x, p())) by Restate

    have(exists(x, p()) |- p()) by LeftExists(base)
    val rhs = thenHave(() |- exists(x, p()) ==> p()) by Restate

    have(thesis) by RightIff(lhs, rhs)
  }

  val existsOneImpliesExists = Theorem(
    existsOne(x, P(x)) |- exists(x, P(x))
  ) {
    have((x === y) <=> P(y) |- (x === y) <=> P(y)) by Hypothesis
    thenHave(forall(y, (x === y) <=> P(y)) |- (x === y) <=> P(y)) by LeftForall
    thenHave(forall(y, (x === y) <=> P(y)) |- P(x)) by InstFunSchema(Map(y -> x))
    // thenHave(forall(y, (x === y) <=> P(x)) |- (x === x) <=> P(x)) by Rewrite
    thenHave(forall(y, (x === y) <=> P(y)) |- exists(x, P(x))) by RightExists
    thenHave(exists(x, forall(y, (x === y) <=> P(y))) |- exists(x, P(x))) by LeftExists
    thenHave(thesis) by Restate
  }

  val equalityTransitivity = Theorem(
    (x === y) /\ (y === z) |- (x === z)
  ) {
    have((x === y) |- (x === y)) by Hypothesis
    thenHave(Set((x === y), (y === z)) |- (x === z)) by RightSubstEq.apply2
    thenHave(thesis) by Restate
  }
}
