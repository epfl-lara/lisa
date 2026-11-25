package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofCarrier.Failure
import lisa.utils.prooflib.ProofCarrier.Success
import lisa.utils.prooflib.ProofHelpers._
import lisa.utils.prooflib.TacticHelpers._
import org.scalatest.funsuite.AnyFunSuite

class ProofCarrierSuite extends AnyFunSuite:
  given Library = new Library
  private val p, q = variable[Prop]

  test("successful extraction preserves the theorem, kernel and payload"):
    val theorem = BasicStep.Restate(p |- p).thm
    val carrier = Success(theorem, 42)
    assert(carrier.isValid)
    assert(carrier.thm eq theorem)
    assert(carrier.kernel eq theorem.kernel)
    assert(carrier.destruct == (theorem, 42))
    assert(!carrier.kernel.usesSorry)

  test("map and flatMap preserve values and propagate a returned failure"):
    val theorem = BasicStep.Restate(p |- p).thm
    val carrier = Success(theorem, 41).map(_ + 1)
    val result = carrier.flatMap((value, proof) => Success(proof, value.toString))
    assert(result.destruct == (theorem, "42"))
    assert(carrier.judgement.destruct == (theorem, ()))
    val failure = Failure("next step failed")
    assert(carrier.flatMap((_, _) => failure) eq failure)

  test("failure propagation never evaluates callbacks or manufactures a theorem"):
    val failure: ProofCarrier[Int] = Failure("no proof")
    assert(!failure.isValid)
    assert(failure.map(_ => fail("map evaluated a failure")) eq failure)
    assert(failure.flatMap((_, _) => fail("flatMap evaluated a failure")) eq failure)
    assert(failure.judgement eq failure)
    assert(intercept[TacticFailureException](failure.thm).getMessage == "no proof")
    assert(intercept[TacticFailureException](failure.kernel).getMessage == "no proof")
    assert(intercept[TacticFailureException](failure.destruct).getMessage == "no proof")

  test("extracting the same failure twice creates distinct exceptions at the extraction sites"):
    val failure = Failure("no proof")
    val first = intercept[TacticFailureException](failure.destruct(using sourcecode.File("first.scala"), sourcecode.Line(10)))
    val second = intercept[TacticFailureException](failure.destruct(using sourcecode.File("second.scala"), sourcecode.Line(20)))
    assert(!(first eq second))
    assert(first.file.value == "first.scala" && first.line.value == 10)
    assert(second.file.value == "second.scala" && second.line.value == 20)
    assert(first.getStackTrace.nonEmpty && second.getStackTrace.nonEmpty)

  test("callback exceptions propagate unchanged"):
    val carrier = BasicStep.Restate(p |- p)
    val bug = new IllegalStateException("broken callback")
    assert(intercept[IllegalStateException](carrier.map(_ => throw bug)) eq bug)
    assert(intercept[IllegalStateException](carrier.flatMap((_, _) => throw bug)) eq bug)

  test("alternatives evaluate only after a failure and retain the selected result"):
    val success = BasicStep.Restate(p |- p)
    val failure = Failure("first attempt")
    val secondFailure = Failure("second attempt")
    assert(success.or(fail("unnecessary alternative")) eq success)
    assert(failure.or(success) eq success)
    assert(failure.or(secondFailure) eq secondFailure)
    val bug = new IllegalArgumentException("broken alternative")
    assert(intercept[IllegalArgumentException](failure.or(throw bug)) eq bug)
    assert((success || fail("unnecessary judgement alternative")) eq success)
    assert((failure || success) eq success)

  test("maybe leaves failed attempts uncommitted and records the successful alternative"):
    val result = ProofBuilder.withContext: proof ?=>
      val failed = maybe(() |- p) by BasicStep.Hypothesis
      assert(!failed.isValid)
      assert(proof.last.isEmpty && proof.errors.isEmpty)
      val selected = failed.or(maybe(p |- p) by BasicStep.Hypothesis)
      assert(proof.last.contains(selected.thm))
      selected
    assert(result.isValid && !result.kernel.usesSorry)

  test("tactic have throws at its source location and leaves the previous theorem intact"):
    ProofBuilder.freshContext(isTactic = true): proof ?=>
      val previous = have(p |- p) by BasicStep.Hypothesis
      var line = 0
      val exception = intercept[TacticFailureException] {
        line = summon[sourcecode.Line].value + 1
        have(() |- p) by BasicStep.Hypothesis
      }
      assert(exception.line.value == line)
      assert(proof.last.contains(previous))
      assert(proof.errors.isEmpty)
      ProofJudgement(previous)

  test("haveM cannot supply a payload for a failed result"):
    ProofBuilder.withContext: proof ?=>
      intercept[TacticFailureException] {
        haveM(p |- p) by ((_: Sequent) => Failure("no payload"))
      }
      assert(proof.last.isEmpty)
      BasicStep.Restate(p |- p)

  test("failWith exits a tactic subproof with a failure value"):
    val result = TacticProofM[Int] {
      failWith("search exhausted")
      fail("continued after failWith")
    }
    assert(result == Failure("search exhausted"))

  test("empty proof completion returns failure rather than admitting a goal"):
    val builder = ProofBuilder.withGoal(p |- q)
    assert(builder.pure(42) == Failure("The proof produced no theorem."))
    assert(builder.last.isEmpty)

  test("kernel lifting preserves front syntax and rejects mismatched conclusions"):
    val theorem = BasicStep.Restate(p |- p).thm
    val valid: Either[Failure, lisa.utils.K.Thm] = Right(theorem.kernel)
    assert(valid.lift(theorem.statement).thm.statement eq theorem.statement)
    intercept[IllegalArgumentException](valid.lift(p |- q))
    val failure = Failure("kernel rejection")
    val invalid: Either[Failure, lisa.utils.K.Thm] = Left(failure)
    assert(invalid.lift(p |- q) eq failure)
