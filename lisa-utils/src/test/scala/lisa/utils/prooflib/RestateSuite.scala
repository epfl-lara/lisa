package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class RestateSuite extends AnyFunSuite:
  given Library = new Library

  private val p, q, r = variable[Prop]
  private val x = variable[Ind]

  test("bare Restate uses the direct kernel rule"):
    for statement <- Seq(p |- p, () |- (x === x), () |- (p \/ !p)) do
      val result = BasicStep.Restate(statement)
      assert(result.isValid, result.errors.mkString("\n"))
      val theorem = result.kernel
      assert(theorem.rule == K.RestateTrue)
      assert(!theorem.usesSorry)
      assert(theorem.assumptions.isEmpty)
      assert(theorem.axioms.isEmpty)

  test("bare Restate does not fall back to a propositional solver"):
    val distributivity = () |- ((p /\ (q \/ r)) <=> ((p /\ q) \/ (p /\ r)))
    assert(!BasicStep.Restate(distributivity).isValid)
    assert(Tautology(distributivity).isValid)

  test("bare Restate rejects a nontrivial unproved goal"):
    val result = BasicStep.Restate(p |- q)
    assert(!result.isValid)
    assert(result.justification.isEmpty)
    assert(result.errors.nonEmpty)

  test("Restate from a premise preserves its dependencies"):
    val premise = lisa.kernel.proof.Assume(using summon[Library].theory)((p |- q).underlying).toOption.get
    val result = BasicStep.Restate.from(premise)(() |- (p ==> q))
    assert(result.isValid, result.errors.mkString("\n"))
    val theorem = result.kernel
    assert(theorem.rule == K.Restate)
    assert(theorem.assumptions == premise.assumptions)
    assert(!theorem.usesSorry)
