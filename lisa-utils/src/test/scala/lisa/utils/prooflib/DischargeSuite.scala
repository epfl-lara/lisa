package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class DischargeSuite extends AnyFunSuite:
  private given library: Library = new Library
  private val p, q, r = variable[Prop]

  private def assume(statement: Sequent): Thm =
    Thm(statement, lisa.kernel.proof.Assume(using library.theory)(statement.underlying).toOption.get)

  test("remove all equivalent assumptions with one checked discharge"):
    val base = assume((p, p /\ p, r) |- q)
    val premise = assume(() |- p)
    val result = Discharge(premise)(base)
    assert(result.isValid)
    assert(result.thm.statement == (r |- q))
    assert(!result.kernel.usesSorry)
    assert(result.kernel.assumptions == base.kernel.assumptions ++ premise.kernel.assumptions)

  test("retain the original theorem when no assumption matches"):
    val base = assume(p |- q)
    val unrelated = assume(() |- r)
    val result = Discharge(unrelated)(base)
    assert(result.isValid && (result.thm eq base))
    assert(result.kernel.assumptions == base.kernel.assumptions)

  test("retain dependencies when the discharge would leave the statement unchanged"):
    val base = assume(p |- q)
    val identity = assume(p |- p)
    val result = Discharge(identity)(base)
    assert(result.isValid && (result.thm eq base))
    assert(result.kernel.assumptions == base.kernel.assumptions)

  test("reject premises without exactly one conclusion"):
    val base = assume(p |- q)
    for statement <- Seq(Sequent(Set.empty, Set.empty), Sequent(Set.empty, Set(p, r))) do
      val result = Discharge(assume(statement))(base)
      assert(!result.isValid && result.errors.nonEmpty)

  test("discharge dependent premises in their supplied order"):
    val base = assume(p |- q)
    val first = assume(r |- p)
    val second = assume(() |- r)
    val result = Discharge(first, second)(base)
    assert(result.isValid && result.thm.statement == (() |- q))
    assert(!result.kernel.usesSorry)
    assert(result.kernel.assumptions == base.kernel.assumptions ++ first.kernel.assumptions ++ second.kernel.assumptions)
