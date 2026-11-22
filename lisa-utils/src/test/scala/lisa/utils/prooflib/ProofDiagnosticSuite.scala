package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import java.nio.file.Files
import java.nio.file.Path

class ProofDiagnosticSuite extends AnyFunSuite:
  private val p = variable[Prop]
  private val goal = () |- p
  private val sourceDirectory = Files.createDirectories(Path.of("target"))

  private def frame(name: String, file: String, line: Int): StackTraceElement =
    new StackTraceElement(name, "apply", file, line)

  private def diagnostic(error: Exception, file: String = "MissingProof.scala", line: Int = 42): ProofDiagnostic =
    ProofDiagnostic(error, sourcecode.File(file), sourcecode.Line(line), goal)

  test("Lisa exceptions show the cause line while retaining recovery metadata internally"):
    val path = Files.createTempFile(sourceDirectory, "proof-diagnostic-", ".scala")
    try
      Files.writeString(path, "object Example:\n  have(p) by tactic\n")
      val error = new TacticFailureException("cannot prove goal")(using sourcecode.Line(2), sourcecode.File(path.toString))
      val report = diagnostic(error, path.toString, 1)
      val rendered = report.format
      assert(rendered.startsWith(s"-- Proof error: ${path.normalize()}:2 "))
      assert(rendered.contains("2 |  have(p) by tactic\n"))
      assert(!rendered.contains("1 |object Example:"))
      assert(rendered.contains("cannot prove goal"))
      assert(!rendered.contains("Admitted:") && !rendered.contains("Recovered at:"))
      assert(report.file.value == path.toString && report.line.value == 1)
      assert(report.conclusion == goal)
    finally Files.deleteIfExists(path)

  test("ordinary exceptions use the first proof-source frame before recovery"):
    val path = Files.createTempFile(sourceDirectory, "proof-diagnostic-", ".scala")
    try
      Files.writeString(path, "object Example:\n  throw new IllegalStateException(\"broken\")\n")
      val error = new IllegalStateException("broken")
      error.setStackTrace(
        Array(
          frame("java.util.Objects", "Objects.java", 1),
          frame("Example", path.getFileName.toString, 2),
          new StackTraceElement(classOf[ProofBuilder].getName, "recover", "Proof.scala", 52),
          frame("Example", path.getFileName.toString, 1)
        )
      )
      val rendered = diagnostic(error, path.toString, 1).format
      assert(rendered.startsWith(s"-- IllegalStateException: ${path.normalize()}:2 "))
      assert(rendered.contains("2 |  throw new IllegalStateException(\"broken\")"))
    finally Files.deleteIfExists(path)

  test("unknown causes do not use the recovery location as a substitute"):
    val error = new IllegalStateException("unknown origin")
    error.setStackTrace(
      Array(
        frame("Unknown", "Other.scala", 9),
        new StackTraceElement(classOf[ProofBuilder].getName, "recover", "Proof.scala", 52),
        frame("Example", "MissingProof.scala", 42)
      )
    )
    val rendered = diagnostic(error).format
    assert(rendered.linesIterator.next().startsWith("-- IllegalStateException ---"))
    assert(!rendered.contains("Recovered at:"))
    assert(!rendered.contains("42 |"))
    assert(rendered.contains("at Unknown.apply(Other.scala:9)"))
    assert(!rendered.contains("Admitted:"))

  test("invalid explicit locations do not fall back to a stack or recovery location"):
    val error = new TacticFailureException("unknown origin")(using sourcecode.Line(0), sourcecode.File(""))
    error.setStackTrace(Array(frame("Example", "MissingProof.scala", 42)))
    val rendered = diagnostic(error).format
    assert(rendered.linesIterator.next().startsWith("-- Proof error ---"))
    assert(!rendered.contains("Recovered at:") && !rendered.contains("42 |"))

  test("coincident cause and recovery locations identify the source once"):
    val error = new TacticFailureException("failed")(using sourcecode.Line(42), sourcecode.File("MissingProof.scala"))
    val rendered = diagnostic(error).format
    assert(rendered.startsWith("-- Proof error: MissingProof.scala:42 "))
    assert(!rendered.contains("Recovered at:"))

  test("traces retain tactic frames through recovery and omit subsequent caller frames"):
    val error = new IllegalStateException("broken tactic")
    val stack = Array(
      frame("Tactic", "Tactic.scala", 12),
      frame("Example", "MissingProof.scala", 42),
      frame("Runner", "Runner.scala", 5),
      frame("ExampleInitializer", "MissingProof.scala", 42)
    )
    error.setStackTrace(stack)
    val report = diagnostic(error)
    val rendered = report.format
    assert(rendered.contains("at Tactic.apply(Tactic.scala:12)"))
    assert(rendered.contains("at Example.apply(MissingProof.scala:42)"))
    assert(!rendered.contains("Runner.apply"))
    assert(rendered.contains("2 outer frames omitted"))
    assert(!rendered.contains("ExampleInitializer"))
    assert(error.getStackTrace.toSeq == stack.toSeq)
    assert(report.format == rendered)

  test("an unmatched recovery location leaves the entire trace visible"):
    val error = new IllegalArgumentException("broken")
    error.setStackTrace(Array(frame("Tactic", "Tactic.scala", 12), frame("Runner", "Runner.scala", 5)))
    val rendered = diagnostic(error).format
    assert(rendered.contains("at Runner.apply(Runner.scala:5)"))
    assert(!rendered.contains("frames omitted"))

  test("missing or invalid source locations do not prevent diagnostics"):
    for (file, line) <- Seq(("MissingProof.scala", 42), ("invalid\u0000path", 1), ("MissingProof.scala", 0)) do
      val rendered = diagnostic(new IllegalStateException("original error"), file, line).format
      assert(rendered.contains("original error"))

  test("source line numbers beyond the end of a file are harmless"):
    val path = Files.createTempFile(sourceDirectory, "proof-diagnostic-", ".scala")
    try
      Files.writeString(path, "short file\n")
      val error = new TacticFailureException("original error")(using sourcecode.Line(20), sourcecode.File(path.toString))
      val rendered = diagnostic(error, path.toString, 20).format
      assert(rendered.contains("original error") && !rendered.contains("20 |"))
    finally Files.deleteIfExists(path)

  test("causes and suppressed exceptions are displayed without modifying their traces"):
    val cause = new IllegalArgumentException("root cause")
    val suppressed = new IllegalStateException("cleanup failed")
    val error = new RuntimeException("outer error", cause)
    error.addSuppressed(suppressed)
    val exceptions = Seq(error, cause, suppressed)
    val stacks = exceptions.map(_.getStackTrace.toSeq)
    val rendered = diagnostic(error).format
    assert(rendered.contains("Caused by: java.lang.IllegalArgumentException: root cause"))
    assert(rendered.contains("Suppressed: java.lang.IllegalStateException: cleanup failed"))
    assert(exceptions.map(_.getStackTrace.toSeq) == stacks)

  test("cyclic causes terminate and exceptions without messages still have a class name"):
    val error = new RuntimeException()
    val cause = new RuntimeException("cause", error)
    error.initCause(cause)
    val rendered = diagnostic(error).format
    assert(rendered.contains("RuntimeException"))
    assert(rendered.contains("[Circular reference:"))

  test("user errors omit exception details without changing the stored stack"):
    class CustomUserError extends lisa.utils.UserLisaException("user message"):
      override def showError: String = "A helpful explanation."
    val error = new CustomUserError
    error.setStackTrace(Array(frame("Example", "MissingProof.scala", 42)))
    val stack = error.getStackTrace.toSeq
    val report = diagnostic(error)
    val rendered = report.format
    assert(rendered.startsWith("-- Proof error:"))
    assert(rendered.contains("A helpful explanation."))
    assert(!rendered.linesIterator.next().contains("CustomUserError"))
    assert(!rendered.contains("Trace:") && !rendered.contains("at Example"))
    assert(report.exception eq error)
    assert(error.getStackTrace.toSeq == stack)

  test("internal tactic errors show the cause trace without the wrapper trace"):
    val cause = new TacticFailureException("internal failed step")
    val error = new TacticException(cause.message, cause)
    error.setStackTrace(Array(frame("Wrapper", "Subproof.scala", 28)))
    cause.setStackTrace(Array(frame("FailedStep", "Tactic.scala", 12), frame("Example", "MissingProof.scala", 42), frame("Runner", "Runner.scala", 5)))
    val stack = cause.getStackTrace.toSeq
    val wrapperStack = error.getStackTrace.toSeq
    val rendered = diagnostic(error).format
    assert(rendered.startsWith("-- Internal tactic error:"))
    assert(rendered.contains("Trace:"))
    assert(!rendered.contains("lisa.utils.prooflib.TacticException: internal failed step"))
    assert(!rendered.contains("at Wrapper"))
    assert(rendered.contains("at FailedStep.apply(Tactic.scala:12)"))
    assert(rendered.contains("at Example.apply(MissingProof.scala:42)"))
    assert(!rendered.contains("at Runner"))
    assert(error.getStackTrace.toSeq == wrapperStack)
    assert(rendered.contains("Caused by: lisa.utils.prooflib.TacticFailureException: internal failed step"))
    assert(cause.getStackTrace.toSeq == stack)

  test("internal tactic errors without a cause retain their own trace"):
    val error = new TacticException("invalid internal state")
    error.setStackTrace(Array(frame("Tactic", "Tactic.scala", 12)))
    val rendered = diagnostic(error).format
    assert(rendered.contains("lisa.utils.prooflib.TacticException: invalid internal state"))
    assert(rendered.contains("at Tactic.apply(Tactic.scala:12)"))
    assert(!rendered.contains("Caused by:"))

  test("omitting a tactic wrapper preserves nested and suppressed exceptions and handles cycles"):
    val nested = new IllegalArgumentException("root cause")
    val cause = new IllegalStateException("failed step", nested)
    val error = new TacticException("tactic bug", cause)
    val suppressed = new RuntimeException("wrapper cleanup")
    error.addSuppressed(suppressed)
    cause.addSuppressed(new RuntimeException("cause cleanup"))
    nested.initCause(error)
    error.setStackTrace(Array(frame("Wrapper", "Subproof.scala", 28)))
    val rendered = diagnostic(error).format
    assert(!rendered.contains("at Wrapper"))
    assert(rendered.contains("Caused by: java.lang.IllegalStateException: failed step"))
    assert(rendered.contains("Caused by: java.lang.IllegalArgumentException: root cause"))
    assert(rendered.contains("Suppressed: java.lang.RuntimeException: wrapper cleanup"))
    assert(rendered.contains("Suppressed: java.lang.RuntimeException: cause cleanup"))
    assert(rendered.contains("[Circular reference:"))
    assert(error.getCause eq cause)
    assert(error.getSuppressed.toSeq == Seq(suppressed))
