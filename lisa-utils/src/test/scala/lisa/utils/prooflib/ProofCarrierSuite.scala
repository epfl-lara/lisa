package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class ProofCarrierSuite extends AnyFunSuite:
  given Library = new Library
  private val p, q = variable[Prop]
  private val error = SoftError("failed step", summon[sourcecode.File], summon[sourcecode.Line])

  test("extract the existing theorem without changing its statement or dependencies"):
    val carrier = BasicStep.Restate(p |- p).map(_ => 42)
    assert(carrier.thm eq carrier.justification.get)
    assert(carrier.kernel eq carrier.justification.get.kernel)
    assert(!carrier.kernel.usesSorry)
    assert(carrier.destruct._2 == 42)

  test("recover a missing justification with Sorry without changing the carrier"):
    val carrier = BasicStep.Restate(p |- q)
    val errors = carrier.errors
    assert(carrier.justification.isEmpty)
    assert(carrier.thm.statement == (p |- q))
    assert(carrier.thm.kernel.usesSorry)
    assert(carrier.kernel.statement == (p |- q).underlying)
    assert(carrier.kernel.usesSorry)
    assert(carrier.justification.isEmpty)
    assert(carrier.errors == errors)
    assert(!carrier.isValid)

  test("retain an existing justification despite accumulated errors"):
    val carrier = BasicStep.Restate(p |- p).withError(error)
    assert(carrier.hasJustification)
    assert(carrier.thm eq carrier.justification.get)
    assert(carrier.kernel eq carrier.justification.get.kernel)
    assert(!carrier.kernel.usesSorry)
    assert(carrier.errors == Set(error))
    assert(!carrier.isValid)

  test("recover an empty soft carrier even without recorded errors"):
    val carrier = ProofCarrier(Set.empty, p |- q, None, ())
    assert(carrier.thm.statement == (p |- q))
    assert(carrier.kernel.usesSorry)
    assert(carrier.errors.isEmpty)
    assert(!carrier.isValid)

  test("retain fatal error information"):
    val fatal = FatalError("fatal step", summon[sourcecode.File], summon[sourcecode.Line])
    val carrier = FatalCarrier(fatal, Set(error))
    assert(intercept[FatalCarrierDestructionException](carrier.thm).carrier eq carrier)
    assert(intercept[FatalCarrierDestructionException](carrier.kernel).carrier eq carrier)

  test("retain explicit recovery at proof boundaries"):
    val carrier = ProofCarrier(Set(error), p |- q, None, 42)
    val (theorem, payload) = carrier.destruct
    assert(theorem.kernel.usesSorry)
    assert(payload == 42)
    val next = carrier.flatMap((value, theorem) => ProofJudgement(theorem).map(_ => value + 1))
    assert(next.errors == Set(error))
    assert(next.destruct._2 == 43)
    assert(next.thm.kernel.usesSorry)
    assert(next.kernel eq next.justification.get.kernel)
    assert(!next.isValid)

  test("preserve every carrier field when adding no errors"):
    val theorem = BasicStep.Restate(p |- p).thm
    val carriers = Seq(
      SoftCarrier(Set.empty[ProofError], theorem.statement, Some(theorem), 42),
      SoftCarrier(Set(error), p |- q, None, 17)
    )
    for carrier <- carriers; empty <- Seq(List.empty[ProofError], Set.empty[ProofError], Vector.empty[ProofError]) do
      val next = carrier.withErrors(empty)
      assert(next.errors == carrier.errors)
      assert(next.statement == carrier.statement)
      assert(next.justification == carrier.justification)
      assert(next.payload == carrier.payload)
      assert(next.isValid == carrier.isValid)

  test("accumulate distinct errors without mutating the original carrier"):
    val extra = SoftError("another failure", summon[sourcecode.File], summon[sourcecode.Line])
    val carrier = SoftCarrier(Set[ProofError](error), p |- q, None, 42)
    val next = carrier.withErrors(List(extra, error, extra))
    assert(carrier.errors == Set(error))
    assert(next.errors == Set(error, extra))
    assert(next.statement == carrier.statement && next.payload == 42)
    assert(next.justification.isEmpty && !next.isValid)

  test("retain the fatal error when appending an empty or nonempty collection"):
    val fatal = FatalError("fatal step", summon[sourcecode.File], summon[sourcecode.Line])
    val carrier = FatalCarrier(fatal, Set.empty)
    assert(carrier.withErrors(Vector.empty) == carrier)
    assert(carrier.withErrors(List(error)) == FatalCarrier(fatal, Set(error)))
