package lisa.hol

import java.io.ByteArrayOutputStream
import java.nio.file.{Files, Path}
import lisa.hol.extractor.*
import org.scalatest.funsuite.AnyFunSuite

class ImportTimingSuite extends AnyFunSuite:
  private val p = "v(timing_p)(c[bool][])"
  private val q = "v(timing_q)(c[bool][])"
  private val equality = s"C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))($p))($p)"

  private def withTrace[A](label: String, mismatch: Boolean = false)(run: String => A): A =
    val directory = Files.createTempDirectory("lisa-import-timing")
    val prefix = directory.resolve("trace").toString
    val paths = Seq("proofs", "theorems", "names").map(suffix => Path.of(s"$prefix.$suffix"))
    val proofs = Seq(ProofLine(0, REFL(p)), ProofLine(1, ASSUME(p)), ProofLine(3, EQ_MP(0, 1)), ProofLine(7, EQ_MP(0, 1)))
    val statements = Seq(
      TheoremStatement(0, RawSequent(Nil, equality)),
      TheoremStatement(1, RawSequent(List(p), p)),
      TheoremStatement(3, RawSequent(List(p), p)),
      TheoremStatement(7, RawSequent(List(p), if mismatch then q else p))
    )
    val names = Seq(TheoremRef(3, s"timing_${label}_first"), TheoremRef(7, s"timing_${label}_second"), TheoremRef(3, s"timing_${label}_alias"))
    try
      Files.writeString(paths(0), proofs.map(upickle.default.write(_)).mkString("\n"))
      Files.writeString(paths(1), statements.map(upickle.default.write(_)).mkString("\n"))
      Files.writeString(paths(2), names.map(upickle.default.write(_)).mkString("\n"))
      run(prefix)
    finally
      paths.foreach(Files.deleteIfExists)
      Files.deleteIfExists(directory)

  test("compute cumulative throughput from total work, not the mean of theorem rates"):
    val timing = Import.TheoremTiming(TheoremRef(7, "rates"), 2, 1000000000L, 10, 4000000000L, true)
    assert(timing.elapsedSeconds == 1d)
    assert(timing.totalSeconds == 4d)
    assert(timing.stepsPerSecond == 2d)
    assert(timing.totalStepsPerSecond == 2.5d)

  test("keep zero-duration and cache-only rates finite"):
    val zero = Import.TheoremTiming(TheoremRef(0, "zero"), 0, 0, 0, 0, true)
    assert(zero.stepsPerSecond == 0d)
    assert(zero.totalStepsPerSecond == 0d)
    val alias = zero.copy(elapsedNanos = 1000000000L, totalSteps = 5, totalElapsedNanos = 2000000000L)
    assert(alias.stepsPerSecond == 0d)
    assert(alias.totalStepsPerSecond == 2.5d)

  test("record each theorem and alias without counting shared steps twice"):
    withTrace("shared"): prefix =>
      val output = new ByteArrayOutputStream
      val timings = Console.withOut(output)(Import.importFromPrefix(prefix, 3, failFast = true))
      assert(timings.map(_.steps) == Vector(3, 1, 0))
      assert(timings.map(_.totalSteps) == Vector(3, 4, 4))
      assert(timings.map(_.theorem.id) == Vector(3L, 7L, 3L))
      assert(timings.forall(_.succeeded))
      assert(timings.forall(t => t.elapsedNanos >= 0 && t.totalElapsedNanos >= t.elapsedNanos))
      assert(timings.sliding(2).forall(pair => pair(1).totalElapsedNanos >= pair(0).totalElapsedNanos + pair(1).elapsedNanos))
      assert(output.toString.contains("Total:"))
      assert(output.toString.contains("Last theorem timing_shared_alias (#3): OK; 0 steps"))

  test("include failed work without charging it to the next theorem"):
    withTrace("failure", mismatch = true): prefix =>
      val timings = Console.withOut(new ByteArrayOutputStream)(Import.importFromPrefix(prefix, 3))
      assert(timings.map(_.steps) == Vector(3, 1, 0))
      assert(timings.map(_.totalSteps) == Vector(3, 4, 4))
      assert(timings.map(_.succeeded) == Vector(true, false, true))

  test("report the failed attempt before propagating a fail-fast exception"):
    withTrace("failfast", mismatch = true): prefix =>
      val output = new ByteArrayOutputStream
      Console.withOut(output):
        assertThrows[Import.FailedTheoremException](Import.importFromPrefix(prefix, 3, failFast = true))
      assert(output.toString.contains("Last theorem timing_failfast_second (#7): FAILED; 1 steps"))

  test("measure only requested names and their newly reconstructed dependencies"):
    withTrace("offset"): prefix =>
      val timings = Console.withOut(new ByteArrayOutputStream)(Import.importFromPrefix(prefix, 1, failFast = true, startAt = 1))
      assert(timings.size == 1)
      assert(timings.head.theorem.id == 7)
      assert(timings.head.steps == 3)
      assert(timings.head.totalSteps == 3)
