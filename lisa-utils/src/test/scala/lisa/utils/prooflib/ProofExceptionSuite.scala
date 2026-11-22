package lisa.utils.prooflib

import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.UserLisaException.InvalidProofOperationException
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers._
import lisa.utils.prooflib.TacticHelpers.failWith
import org.scalatest.funsuite.AnyFunSuite

class ProofExceptionSuite extends AnyFunSuite:
  private given Library = new Library
  private given OutputManager = new StringOutputManager
  private val p = variable[Prop]
  private val x = variable[Ind]

  test("custom user and tactic exceptions can extend and override the diagnostics"):
    class CustomUserException extends UserLisaException("user mistake"):
      override def showError: String = "custom user diagnostic"
    class CustomFailure extends TacticFailureException("search failed")
    class CustomTacticException extends TacticException("broken tactic"):
      override def showError: String = "custom tactic diagnostic"
    assert(new CustomUserException().showError == "custom user diagnostic")
    assert(new CustomFailure().showError == "search failed")
    val internal: LisaException = new CustomTacticException
    assert(internal.showError == "custom tactic diagnostic")
    assert(!internal.isInstanceOf[UserLisaException])

  test("wrapping an internal exception retains its cause and original stack"):
    val cause = new IllegalStateException("bad state")
    val stack = cause.getStackTrace
    val error = new TacticException("tactic failed", cause)(using sourcecode.Line(12), sourcecode.File("tactic.scala"))
    assert(error.getCause eq cause)
    assert(cause.getStackTrace.toSeq == stack.toSeq)
    assert(error.file.value == "tactic.scala" && error.line.value == 12)
    assert(error.showError.contains("tactic failed"))

  test("invalid instantiation reports a user error at the caller"):
    val premise = BasicStep.Hypothesis(p |- p).thm
    var expectedLine = 0
    val error = intercept[InvalidProofOperationException] {
      expectedLine = summon[sourcecode.Line].value + 1
      premise.of(x)
    }
    assert(error.line.value == expectedLine)
    assert(error.file.value.endsWith("ProofExceptionSuite.scala"))
    assert(error.showError.contains("non-universal"))

  test("missing proof context is frontend misuse rather than tactic failure"):
    ProofBuilder.freshContext(isTactic = true): proof ?=>
      var expectedLine = 0
      val error = intercept[InvalidProofOperationException] {
        expectedLine = summon[sourcecode.Line].value + 1
        lastStep
      }
      assert(error.line.value == expectedLine)
      intercept[InvalidProofOperationException](thesis)
      intercept[InvalidProofOperationException](goal)
      intercept[InvalidProofOperationException](thenHave(p |- p) by BasicStep.Weakening)
      intercept[InvalidProofOperationException](thenHaveM(p |- p) by ((_: Sequent, _: Thm) => ProofCarrier.Failure("unused")))
      intercept[InvalidProofOperationException](andThen((premise: Thm) => ProofJudgement(premise)))
      assert(proof.last.isEmpty && proof.errors.isEmpty)
      BasicStep.Hypothesis(p |- p)

  test("an empty theorem records UnimplementedProof and registers an admitted theorem"):
    val name = "ProofExceptionSuite.empty"
    val theorem = Theorem.named(name)(p |- p) { () }
    assert(theorem.errors.size == 1)
    val error = theorem.errors.head.exception.asInstanceOf[UnimplementedProof]
    assert(error.name == name && error.statement == (p |- p))
    assert(error.showError.contains(name))
    assert(theorem.thm.usesSorry && theorem.statement == (p |- p))
    assert(summon[Library].theorems.getFull(name).contains(theorem))

  test("rejected definitions are user errors and preserve their declaration location"):
    val library = new Library
    val error = intercept[UserInvalidDefinitionException] {
      given sourcecode.Line = sourcecode.Line(23)
      given sourcecode.File = sourcecode.File("definitions.scala")
      library.define("openDefinition", x)
    }
    assert(error.symbol == "openDefinition")
    assert(error.line.value == 23 && error.file.value == "definitions.scala")
    library.define("closedDefinition", λ(x, x))
    val duplicate = intercept[UserInvalidDefinitionException](library.define("closedDefinition", λ(x, x)))
    assert(duplicate.isInstanceOf[library.AlreadyDefined])

  test("carriers propagate classified exceptions and runtime failures unchanged"):
    val success = BasicStep.Hypothesis(p |- p)
    val errors = Seq(
      new TacticException("already classified"),
      new InterruptedException("interrupted"),
      new java.util.concurrent.CancellationException("cancelled"),
      new OutOfMemoryError("simulated; no allocation attempted")
    )
    for error <- errors do
      assert(intercept[Throwable](success.map(_ => throw error)) eq error)
      assert(intercept[Throwable](success.flatMap((_, _) => throw error)) eq error)

  test("tactic boundaries preserve ordinary failures and early failure exits"):
    val failure = ProofCarrier.Failure("search failed")
    assert(TacticProof { failure } eq failure)
    assert(TacticProofM[Int] { failure } eq failure)
    assert(TacticProof { failWith("stop") } == ProofCarrier.Failure("stop"))
    assert(TacticProofM[Int] { failWith("stop") } == ProofCarrier.Failure("stop"))

  test("tactic boundaries reclassify frontend exceptions while preserving their cause and location"):
    val original = new InvalidProofOperationException("bad use")(using sourcecode.Line(12), sourcecode.File("tactic.scala"))
    val stack = original.getStackTrace.toSeq
    val errors = Seq(
      intercept[TacticException](TacticProof { throw original }),
      intercept[TacticException](TacticProofM[Int] { throw original })
    )
    for error <- errors do
      assert(error.getCause eq original)
      assert(error.line.value == 12 && error.file.value == "tactic.scala")
      assert(error.showError.contains("bad use"))
    assert(original.getStackTrace.toSeq == stack)

  test("ordinary exceptions escaping tactics are wrapped and already classified exceptions are not"):
    val original = new IllegalStateException("broken implementation")
    val stack = original.getStackTrace.toSeq
    var inner: TacticException = null
    val error = intercept[TacticException] {
      TacticProof {
        try TacticProofM[Int] { throw original }.judgement
        catch
          case caught: TacticException =>
            inner = caught
            throw caught
      }
    }
    assert(error eq inner)
    assert(error.getCause eq original)
    assert(original.getStackTrace.toSeq == stack)
    assert(intercept[TacticException](TacticProofM[Int] { throw error }) eq error)

  test("independent user subproofs do not reclassify exceptions"):
    val error = new InvalidProofOperationException("user mistake")
    assert(intercept[InvalidProofOperationException](Subproof { throw error }) eq error)
    assert(intercept[InvalidProofOperationException](SubproofM[Int] { throw error }) eq error)

  test("tactic classification lets runtime errors and external boundary breaks propagate"):
    val errors = Seq(new InterruptedException("stop"), new OutOfMemoryError("simulated"), new AssertionError("bug"))
    for error <- errors do
      assert(intercept[Throwable](TacticProof { throw error }) eq error)
      assert(intercept[Throwable](TacticProofM[Int] { throw error }) eq error)
    val result = scala.util.boundary[Int] {
      TacticProof { scala.util.boundary.break(7) }
      0
    }
    assert(result == 7)
