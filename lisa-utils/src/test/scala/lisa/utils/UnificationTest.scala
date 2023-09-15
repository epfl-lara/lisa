package lisa.utils

import lisa.utils.ProofTacticTestLib
import lisa.utils.unification.UnificationUtils.*
import org.scalatest.funsuite.AnyFunSuite

/**
 * Tests for the unification library, includes first-order unification and
 * matching, and second-order matching.
 */
class UnificationTest extends ProofTacticTestLib {

  /**
   * Matching tests
   */

  test("Unification Tests: First-Order Matching on Terms") {

    val f = function(2)
    val g = function(2)
    val h = function(1)
    val x = variable
    val y = variable
    val z = variable

    // TODO: Generate random terms, apply a random substitution and try to retrieve it?

    val correct: List[(Term, Term, Option[Map[VariableLabel, Term]])] = List(
      (f(x, y), f(x, x), Some(Map(y -> x))),
      (f(x, y), f(x, y), Some(Map())),
      (f(x, x), f(x, x), Some(Map())),
      (x, y, Some(Map(x -> y))),
      (x, f(x, y), Some(Map(x -> f(x, y)))),
      (x, x, Some(Map())),
      (f(x, g(y, y)), f(y, g(x, x)), Some(Map(x -> y, y -> x))),
      (f(x, g(y, y)), f(y, g(y, y)), Some(Map(x -> y))),
      (f(x, g(y, y)), f(z, g(z, z)), Some(Map(x -> z, y -> z))),
      (f(x, g(y, x)), f(z, g(z, z)), Some(Map(x -> z, y -> z))),
      (f(x, g(y, x)), f(y, g(x, y)), Some(Map(x -> y, y -> x)))
    )

    val incorrect: List[(Term, Term, Option[Map[VariableLabel, Term]])] = List(
      (f(x, y), g(x, y), None),
      (f(x, y), h(x), None),
      (f(x, y), x, None),
      (f(z, g(z, z)), f(x, g(y, y)), None)
    )

    for ((t1, t2, res) <- (correct ++ incorrect))
      if (matchTerm(t2, t1) == res) true
      else fail(s"Matching test failed:\nFirst Term: $t1\nSecond Term: $t2\nExpected Result: $res\nFound: ${matchTerm(t1, t2)}\n")
  }

  test("Unification Tests: First-Order Matching on Formulas") {

    val f = function(2)
    val g = function(2)
    val h = function(1)
    val x = variable
    val y = variable
    val z = variable

    val P = predicate(1)
    val Q = predicate(2)
    val phi = formulaVariable
    val psi = formulaVariable
    val chi = formulaVariable

    val correct: List[(Formula, Formula, Option[(Map[VariableFormulaLabel, Formula], Map[VariableLabel, Term])])] = List(
      (P(f(x, y)), P(f(x, x)), Some(Map(), Map(y -> x))),
      (phi, P(f(x, y)), Some(Map(phi -> P(f(x, y))), Map())),
      (phi, chi, Some(Map(phi -> chi), Map())),
      (P(x), P(x), Some(Map(), Map())),
      (P(x), P(g(x, y)), Some(Map(), Map(x -> g(x, y)))),
      (phi /\ chi, P(x) /\ Q(x, y), Some(Map(phi -> P(x), chi -> Q(x, y)), Map())),
      (exists(x, P(x)), exists(y, P(y)), Some(Map(), Map()))
    )

    val incorrect: List[(Formula, Formula, Option[(Map[VariableFormulaLabel, Formula], Map[VariableLabel, Term])])] = List(
      (P(f(x, y)), P(h(x)), None),
      (exists(x, phi), exists(x, P(x)), None),
      (exists(x, P(x)), exists(x, P(y)), None)
    )

    for ((t1, t2, res) <- (correct ++ incorrect))
      if (matchFormula(t2, t1) == res) true
      else fail(s"Matching test failed:\nFirst Formula: $t1\nSecond Formula: $t2\nExpected Result: $res\nFound: ${matchFormula(t1, t2)}\n")
  }

  /**
   * (Actual) Unification tests
   */

  // test("Unification Tests: First-Order Unification of Terms") {

  //   val f = function(2)
  //   val g = function(2)
  //   val h = function(1)
  //   val x = variable
  //   val y = variable
  //   val z = variable

  //   val correct: List[(Term, Term, Option[Map[VariableLabel, Term]])] = List(
  //     (f(x, y), f(x, x), Some(Map(y -> x))),
  //     (f(x, x), f(x, y), Some(Map(x -> y))),
  //     (f(x, g(x, z)), f(x, y), Some(Map(y -> g(x, z)))),
  //     (f(x, y), f(x, y), Some(Map())),
  //     (f(x, x), f(x, x), Some(Map())),
  //     (x, y, Some(Map(x -> y))),
  //     (x, x, Some(Map())),
  //     (x, f(z, y), Some(Map(x -> f(z, y)))),
  //     (f(x, g(y, y)), f(y, g(x, x)), Some(Map(x -> y, y -> x))),
  //     (f(x, g(y, y)), f(y, g(y, y)), Some(Map(x -> y))),
  //     (f(x, g(y, y)), f(z, g(z, z)), Some(Map(x -> z, y -> z))),
  //     (f(x, g(y, x)), f(z, g(z, z)), Some(Map(x -> z, y -> z))),
  //     (f(x, g(y, x)), f(y, g(x, y)), Some(Map(x -> y, y -> x)))
  //   )

  //   val incorrect: List[(Term, Term, Option[Map[VariableLabel, Term]])] = List(
  //     (f(y, y), f(x, y), None),
  //     (f(x, y), g(x, y), None),
  //     (f(x, y), h(x), None),
  //     (f(z, g(z, z)), f(x, g(y, y)), None),
  //     (f(x, y), x, None),
  //     (x, f(x, y), None)
  //   )

  //   for ((t1, t2, res) <- (correct ++ incorrect))
  //     if (unifyTerm(t1, t2) == res) true
  //     else fail(s"Unification test failed:\nFirst Term: $t1\nSecond Term: $t2\nExpected Result: $res\nFound: ${unifyTerm(t1, t2)}\n")
  // }

  // test("Unification Tests: First-Order Unification of Formulas") {

  //   val f = function(2)
  //   val g = function(2)
  //   val h = function(1)
  //   val x = variable
  //   val y = variable
  //   val z = variable

  //   val P = predicate(1)
  //   val Q = predicate(2)
  //   val phi = formulaVariable
  //   val psi = formulaVariable
  //   val chi = formulaVariable

  //   val correct: List[(Formula, Formula, Option[(Map[VariableFormulaLabel, Formula], Map[VariableLabel, Term])])] = List(
  //     (P(f(x, y)), P(f(x, x)), Some(Map(), Map(y -> x))),
  //     (P(f(x, x)), P(f(x, y)), Some(Map(), Map(x -> y))),
  //     (phi, P(f(x, y)), Some(Map(phi -> P(f(x, y))), Map())),
  //     (phi, chi, Some(Map(phi -> chi), Map())),
  //     (P(x), P(x), Some(Map(), Map())),
  //     (phi /\ chi, P(x) /\ Q(x, y), Some(Map(phi -> P(x), chi -> Q(x, y)), Map())),
  //     (exists(x, P(x)), exists(y, P(y)), Some(Map(), Map()))
  //   )

  //   val incorrect: List[(Formula, Formula, Option[(Map[VariableFormulaLabel, Formula], Map[VariableLabel, Term])])] = List(
  //     (P(f(x, y)), P(h(x)), None),
  //     (P(h(x)), P(f(x, y)), None),
  //     (exists(x, phi), exists(x, P(x)), None),
  //     (exists(x, P(x)), exists(x, P(y)), None),
  //     (phi, phi /\ psi, None),
  //     (P(x), P(g(x, y)), None)
  //   )

  //   for ((t1, t2, res) <- (correct ++ incorrect))
  //     if (unifyFormula(t1, t2) == res) true
  //     else fail(s"Unification test failed:\nFirst Formula: $t1\nSecond Formula: $t2\nExpected Result: $res\nFound: ${unifyFormula(t1, t2)}\n")
  // }
}
