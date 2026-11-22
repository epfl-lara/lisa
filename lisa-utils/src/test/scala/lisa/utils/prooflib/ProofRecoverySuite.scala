package lisa.utils.prooflib

import lisa.utils.UserLisaException.InvalidProofOperationException
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofCarrier.Failure
import lisa.utils.prooflib.ProofCarrier.Success
import lisa.utils.prooflib.ProofHelpers._
import lisa.utils.prooflib.TacticHelpers._
import org.scalatest.funsuite.AnyFunSuite

class ProofRecoverySuite extends AnyFunSuite:
  private given Library = new Library
  private val output = new StringOutputManager
  private given OutputManager = output
  private val p, q = variable[Prop]
  private val x = variable[Ind]

  test("a user have admits a returned failure in its assumption context and continues"):
    ProofBuilder.withContext: proof ?=>
      ProofHelpers.assume(q)
      var expectedLine = 0
      expectedLine = summon[sourcecode.Line].value + 1
      val admitted = have(p) by ((_: Sequent) => Failure("search exhausted"))
      assert(admitted.statement == (q |- p))
      assert(admitted.usesSorry && proof.last.contains(admitted))
      val error = proof.errors.head
      assert(error.exception.isInstanceOf[TacticFailureException])
      assert(error.line.value == expectedLine)
      assert(error.conclusion == admitted.statement)
      have(p) by BasicStep.Weakening(admitted)
      assert(proof.errors.size == 1)
      ProofJudgement(admitted)

  test("user have preserves Lisa exceptions without wrapping or deduplicating them"):
    ProofBuilder.withContext: proof ?=>
      val exception = new InvalidProofOperationException("broken implementation")
      val stack = exception.getStackTrace.toSeq
      for _ <- 1 to 2 do have(p) by ((_: Sequent) => throw exception)
      assert(proof.errors.size == 2)
      assert(proof.errors.forall(_.exception eq exception))
      assert(exception.getStackTrace.toSeq == stack)
      ProofJudgement(lastStep)

  test("tactic proofs abort at an internal failed have and the user step recovers"):
    ProofBuilder.withContext: user ?=>
      var internalContinued = false
      var internal: Option[ProofBuilder] = None
      def broken(conclusion: Sequent): ProofJudgement = TacticProof {
        internal = Some(currentProof)
        have(conclusion) by ((_: Sequent) => Failure("internal failure"))
        internalContinued = true
        have(conclusion) by BasicStep.Sorry
      }
      val admitted = have(p) by broken
      assert(admitted.usesSorry && !internalContinued)
      assert(internal.get.isTactic && internal.get.errors.isEmpty && internal.get.last.isEmpty)
      assert(user.errors.size == 1 && user.errors.head.exception.isInstanceOf[TacticException])
      assert(user.errors.head.exception.getCause.isInstanceOf[TacticFailureException])
      ProofJudgement(admitted)

  test("nested subproofs inherit tactic provenance and do not recover"):
    var childWasTactic = false
    val error = intercept[TacticException] {
      TacticProof {
        have(p) subproof {
          childWasTactic = currentProof.isTactic
          have(p) by ((_: Sequent) => Failure("nested failure"))
        }
      }
    }
    assert(childWasTactic)
    assert(error.getCause.isInstanceOf[TacticFailureException])

  test("user subproofs transfer earlier diagnostics even when a later exception aborts them"):
    ProofBuilder.withContext: parent ?=>
      val aborted = new InvalidProofOperationException("abort subproof")
      val admitted = have(p) subproof {
        assert(!currentProof.isTactic)
        have(q) by ((_: Sequent) => Failure("first failure"))
        throw aborted
      }
      assert(admitted.usesSorry)
      assert(parent.errors.map(_.message).toVector == Vector("first failure", "abort subproof"))
      assert(parent.errors.last.exception eq aborted)
      ProofJudgement(admitted)

  test("a subproof accepts a returned instantiated theorem without recorded steps"):
    val predicate = variable[Ind >>: Prop]
    val formula = forall(x, predicate(x))
    val source = BasicStep.Hypothesis(formula |- formula).thm
    val instance = source.of(x)
    ProofBuilder.withContext: proof ?=>
      proof.assume(q)
      val result = have(instance.statement) subproof { source.of(x) }
      assert(result.statement == proof.withAssumptions(instance.statement))
      assert(!result.usesSorry && proof.errors.isEmpty)
      assert(proof.last.contains(result))
      ProofJudgement(result)

  test("a returned theorem takes precedence over the last recorded subproof step"):
    val source = BasicStep.Hypothesis(p |- p).thm
    ProofBuilder.withContext: proof ?=>
      val result = have(p |- p) subproof {
        have(q) by BasicStep.Sorry
        source
      }
      assert(result.statement == (p |- p))
      assert(!result.usesSorry && proof.errors.isEmpty)
      ProofJudgement(result)

  test("an incompatible returned theorem is checked instead of using a preceding step"):
    val source = BasicStep.Hypothesis(q |- q).thm
    ProofBuilder.withContext: proof ?=>
      val result = have(p) subproof {
        have(p) by BasicStep.Sorry
        source
      }
      assert(result.statement == (() |- p) && result.usesSorry)
      assert(proof.errors.size == 1)
      assert(proof.errors.head.exception.isInstanceOf[TacticFailureException])
      assert(proof.errors.head.message.contains("Subproof does not prove the requested conclusion"))
      ProofJudgement(result)

  test("frontend argument evaluation is recovered by the enclosing subproof"):
    ProofBuilder.withContext: parent ?=>
      var continuedInside = false
      val admitted = have(p) subproof {
        val premise = have(q |- q) by BasicStep.Hypothesis
        have(p) by BasicStep.Restate.from(premise.of(x))
        continuedInside = true
      }
      assert(!continuedInside && admitted.usesSorry)
      assert(parent.errors.size == 1)
      assert(parent.errors.head.exception.isInstanceOf[InvalidProofOperationException])
      assert(parent.errors.head.conclusion == (() |- p))
      ProofJudgement(admitted)

  test("haveM propagates missing payloads to a surrounding user subproof"):
    ProofBuilder.withContext: parent ?=>
      var usedPayload = false
      val admitted = have(p) subproof {
        val (_, value) = haveM(p) by ((_: Sequent) => Failure("no payload"): ProofCarrier[Int])
        usedPayload = true
        assert(value == 0)
      }
      assert(!usedPayload && admitted.usesSorry)
      assert(parent.errors.size == 1 && parent.errors.head.message == "no payload")
      val (_, value) = haveM(p |- p) by ((goal: Sequent) => BasicStep.Hypothesis(goal).map(_ => 42))
      assert(value == 42)
      ProofJudgement(admitted)

  test("steps without a conclusion propagate without logging"):
    ProofBuilder.withContext: proof ?=>
      intercept[TacticFailureException](have(Failure("unknown conclusion")))
      have(p |- p) by BasicStep.Hypothesis
      intercept[TacticFailureException](andThen((_: Thm) => Failure("unknown next conclusion")))
      intercept[TacticFailureException](thenHaveM(p) by ((_: Sequent, _: Thm) => Failure("missing payload")))
      assert(proof.errors.isEmpty && !lastStep.usesSorry)
      ProofJudgement(lastStep)

  test("thenHave recovers failures with its known conclusion"):
    ProofBuilder.withContext: proof ?=>
      have(q |- q) by BasicStep.Hypothesis
      val admitted = thenHave(p) by ((_: Sequent, _: Thm) => Failure("next step failed"))
      assert(admitted.usesSorry && proof.errors.size == 1)
      ProofJudgement(admitted)

  test("maybe and alternatives neither recover nor log exceptions"):
    ProofBuilder.withContext: proof ?=>
      val exception = new IllegalStateException("speculative bug")
      assert(intercept[IllegalStateException](maybe(p) by ((_: Sequent) => throw exception)) eq exception)
      val attempt = maybe(p) by ((_: Sequent) => Failure("expected failure"))
      assert(intercept[IllegalStateException](attempt.or(throw exception)) eq exception)
      assert(proof.errors.isEmpty && proof.last.isEmpty)
      BasicStep.Hypothesis(p |- p)

  test("ordinary exceptions escape user steps and subproofs without admission"):
    val exceptions = Seq(new IllegalStateException("user helper"), new java.util.concurrent.CancellationException("cancelled"))
    for exception <- exceptions do
      ProofBuilder.withContext: proof ?=>
        assert(intercept[Exception](have(p) by ((_: Sequent) => throw exception)) eq exception)
        assert(intercept[Exception](have(p) subproof { throw exception }) eq exception)
        assert(proof.errors.isEmpty && proof.last.isEmpty)
        BasicStep.Hypothesis(p |- p)

  test("a tactic exception with a missing payload is recovered by the enclosing subproof"):
    ProofBuilder.withContext: parent ?=>
      val original = new IllegalStateException("missing payload")
      var usedPayload = false
      def broken(conclusion: Sequent): ProofCarrier[Int] = TacticProofM[Int] { throw original }
      val admitted = have(p) subproof {
        val (_, value) = haveM(p) by broken
        usedPayload = true
        assert(value == 0)
      }
      assert(!usedPayload && admitted.usesSorry)
      assert(parent.errors.size == 1)
      assert(parent.errors.head.exception.isInstanceOf[TacticException])
      assert(parent.errors.head.exception.getCause eq original)
      ProofJudgement(admitted)

  test("runtime failures pass through user recovery without recording or admission"):
    val exceptions = Seq(
      new InterruptedException("interrupted"),
      new OutOfMemoryError("simulated; no allocation attempted"),
      new AssertionError("not an ordinary exception")
    )
    for exception <- exceptions do
      ProofBuilder.withContext: proof ?=>
        assert(intercept[Throwable](have(p) by ((_: Sequent) => throw exception)) eq exception)
        assert(proof.errors.isEmpty && proof.last.isEmpty)
        BasicStep.Hypothesis(p |- p)

  test("failWith control flow crosses a user have without becoming a diagnostic"):
    val result = SubproofM[Int] {
      have(p) by ((_: Sequent) => failWith[Int]("early exit"))
      fail("continued after failWith")
    }
    assert(result == Failure("early exit"))

  test("tactic payload proofs are independent and retain failWith support"):
    ProofBuilder.withContext: parent ?=>
      ProofHelpers.assume(q)
      val result = TacticProofM[Int] {
        assert(currentProof.isTactic && currentProof.assumptions.isEmpty)
        val theorem = have(p |- p) by BasicStep.Hypothesis
        Success(theorem, 7)
      }
      assert(result.destruct._2 == 7 && !result.thm.usesSorry)
      assert(TacticProofM[Int] { failWith("stop") } == Failure("stop"))
      assert(!parent.isTactic)
      result

  test("theorems report recovered exceptions in occurrence order without copying them on reuse"):
    val first = new InvalidProofOperationException("first diagnostic")
    val second = new TacticException("second diagnostic")
    val theorem = Theorem.generated(p) {
      have(p) by ((_: Sequent) => throw first)
      have(p) by ((_: Sequent) => throw second)
    }
    assert(theorem.errors.map(_.exception) == Vector(first, second))
    assert(theorem.thm.usesSorry)
    val printed = output.toString
    assert(printed.indexOf("first diagnostic") < printed.indexOf("second diagnostic"))
    val reused = Theorem.generated(p) { have(theorem) }
    assert(reused.errors.isEmpty && reused.thm.usesSorry)

  test("ordinary nested user failures transfer once and retain user mode"):
    val theorem = Theorem.generated(p) {
      have(p) subproof {
        have(p) subproof {
          assert(!currentProof.isTactic)
          have(p) by ((_: Sequent) => Failure("one occurrence"))
        }
      }
    }
    assert(theorem.errors.size == 1 && theorem.errors.head.message == "one occurrence")

  test("theorem recovery catches frontend argument errors and permits later declarations"):
    var continued = false
    var expectedLine = 0
    expectedLine = summon[sourcecode.Line].value + 1
    val theorem = Theorem.generated(p) {
      val premise = have(q |- q) by BasicStep.Hypothesis
      have(p) by BasicStep.Restate.from(premise.of(x))
      continued = true
    }
    assert(!continued && theorem.thm.usesSorry)
    assert(theorem.thm.statement == (() |- p))
    assert(theorem.errors.size == 1)
    assert(theorem.errors.head.exception.isInstanceOf[InvalidProofOperationException])
    assert(theorem.errors.head.line.value == expectedLine)
    val next = Theorem.generated(p |- p) { have(thesis) by BasicStep.Hypothesis }
    assert(next.errors.isEmpty && !next.thm.usesSorry)

  test("theorem fallback retains earlier diagnostics and admits only the declared goal"):
    val exception = new InvalidProofOperationException("outside a have")
    val theorem = Theorem.generated(p) {
      ProofHelpers.assume(q)
      have(p) by ((_: Sequent) => Failure("earlier failure"))
      throw exception
    }
    assert(theorem.errors.map(_.message) == Vector("earlier failure", "outside a have"))
    assert(theorem.errors.last.exception eq exception)
    assert(theorem.errors.head.conclusion == (q |- p))
    assert(theorem.errors.last.conclusion == (() |- p))
    assert(theorem.thm.statement == (() |- p) && theorem.thm.usesSorry)

  test("theorem fallback handles returned failures and incompatible final conclusions"):
    val failed = Theorem.generated(p) { Failure("returned failure") }
    val mismatched = Theorem.generated(p) { BasicStep.Hypothesis(q |- q) }
    for theorem <- Seq(failed, mismatched) do
      assert(theorem.errors.size == 1 && theorem.errors.head.exception.isInstanceOf[TacticFailureException])
      assert(theorem.thm.statement == (() |- p) && theorem.thm.usesSorry)
    assert(failed.errors.head.message == "returned failure")
    assert(mismatched.errors.head.message.contains("cannot be weakened"))

  test("a missing payload aborts the theorem body without manufacturing a value"):
    var continued = false
    val theorem = Theorem.generated(p) {
      val (_, value) = haveM(p) by ((_: Sequent) => Failure("missing payload"))
      continued = true
      value
    }
    assert(!continued && theorem.thm.usesSorry)
    assert(theorem.errors.size == 1 && theorem.errors.head.message == "missing payload")

  test("the nearest user subproof recovers without a second theorem diagnostic"):
    var continued = false
    val exception = new TacticException("subproof failure")
    val theorem = Theorem.generated(p) {
      have(p) subproof { throw exception }
      continued = true
      lastStep
    }
    assert(continued && theorem.thm.usesSorry)
    assert(theorem.errors.size == 1 && (theorem.errors.head.exception eq exception))

  test("theorem fallback does not intercept ordinary exceptions, runtime errors or boundary control flow"):
    val errors = Seq(
      new IllegalStateException("user helper"),
      new java.util.concurrent.CancellationException("cancelled"),
      new InterruptedException("stop"),
      new OutOfMemoryError("simulated"),
      new AssertionError("bug")
    )
    for error <- errors do
      val count = summon[Library].theorems.all.size
      assert(intercept[Throwable](Theorem.generated(p) { throw error }) eq error)
      assert(summon[Library].theorems.all.size == count)
    val result = scala.util.boundary[Int] {
      Theorem.generated(p) { scala.util.boundary.break(7) }
      0
    }
    assert(result == 7)
