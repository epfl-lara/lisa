package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers._
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks quantified instantiation through the public theorem shorthand.
 */
class QuantifiedInstantiationSuite extends AnyFunSuite:
  private given Library = new Library
  private given OutputManager = new StringOutputManager
  private val x, y, a, b = variable[Ind]
  private val P = variable[Ind >>: Ind >>: Prop]

  private def assertProved(theorem: Thm, expected: Sequent): Unit =
    assert(theorem.statement == expected)
    assert(!theorem.kernel.usesSorry)

  test("instantiate named, front and kernel theorems while retaining assumptions"):
    val formula = forall(x, forall(y, P(x)(y)))
    val named = Theorem(formula |- formula) {
      have(thesis) by BasicStep.Hypothesis
    }
    assert(named.errors.isEmpty)
    for result <- Seq(named.of(a, b), named.thm.of(a, b), named.kernel.of(a, b)) do assertProved(result, formula |- P(a)(b))

  test("partial instantiation avoids capturing a later bound variable"):
    val formula = forall(x, forall(y, P(x)(y)))
    val source = BasicStep.Hypothesis(formula |- formula).thm
    val partial = source.of(y)
    assert(partial.right.head.freeVars.contains(y))
    assertProved(partial.of(a), formula |- P(y)(a))

  test("mixed arguments apply simultaneous substitutions before quantified instantiation"):
    val formula = forall(x, P(a)(x))
    val source = BasicStep.Hypothesis(formula |- formula).thm
    for arguments <- Seq(Seq(a := b, b := a, a), Seq(a, b := a, a := b)) do assertProved(source.of(arguments*), forall(x, P(b)(x)) |- P(b)(a))
    assertProved(source.of(a := b, b := a).of(a), forall(x, P(b)(x)) |- P(b)(a))

  test("empty instantiation retains the original theorem"):
    val source = BasicStep.Hypothesis(P(a)(b) |- P(a)(b)).thm
    assert(source.of() eq source)

  test("invalid quantified arguments fail rather than returning an admitted theorem"):
    val formula = forall(x, P(x)(b))
    val source = BasicStep.Hypothesis(formula |- formula).thm
    intercept[IllegalArgumentException](source.of(a, b))
    intercept[IllegalArgumentException](source.of(a).of(b))
    val multiple = BasicStep.Hypothesis(formula |- (formula, P(a)(b))).thm
    intercept[IllegalArgumentException](multiple.of(a))

  test("instantiation preserves an existing sorry dependency"):
    val source = BasicStep.Sorry(() |- forall(x, P(x)(b))).thm
    val instance = source.of(a)
    assert(instance.statement == (() |- P(a)(b)))
    assert(instance.kernel.usesSorry)
