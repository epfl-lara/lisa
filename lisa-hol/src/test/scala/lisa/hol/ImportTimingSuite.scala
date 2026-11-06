package lisa.hol

import java.io.ByteArrayOutputStream
import java.nio.file.{Files, Path}
import lisa.hol.extractor.*
import org.scalatest.funsuite.AnyFunSuite

class ImportTimingSuite extends AnyFunSuite:
  private val p = "v(timing_p)(c[bool][])"
  private val q = "v(timing_q)(c[bool][])"
  private val equality = s"C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))($p))($p)"
  private var nextId = 10000L

  private def withTrace[A](label: String, mismatch: Boolean = false, composite: Boolean = false)(run: String => A): A =
    val directory = Files.createTempDirectory("lisa-import-timing")
    val offset = nextId
    nextId += 10
    val prefix = directory.resolve("trace").toString
    val paths = Seq("proofs", "theorems", "names").map(suffix => Path.of(s"$prefix.$suffix"))
    val term = if composite then equality else p
    val reflexivity = if composite then s"C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))($term))($term)" else equality
    val proofs = Seq(ProofLine(offset, REFL(term)), ProofLine(offset + 1, ASSUME(term)), ProofLine(offset + 3, EQ_MP(offset, offset + 1)), ProofLine(offset + 7, EQ_MP(offset, offset + 1)))
    val statements = Seq(
      TheoremStatement(offset, RawSequent(Nil, reflexivity)),
      TheoremStatement(offset + 1, RawSequent(List(term), term)),
      TheoremStatement(offset + 3, RawSequent(List(term), term)),
      TheoremStatement(offset + 7, RawSequent(List(term), if mismatch then q else term))
    )
    val names = Seq(TheoremRef(offset + 3, s"timing_${label}_first"), TheoremRef(offset + 7, s"timing_${label}_second"), TheoremRef(offset + 3, s"timing_${label}_alias"))
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

  test("retain startup configuration after properties change"):
    val original = Config.precomputeLemmas
    val key = "lisa.hol.precomputeLemmas"
    val previous = sys.props.get(key)
    try
      sys.props(key) = (!original).toString
      assert(Config.precomputeLemmas == original)
    finally
      previous match
        case Some(value) => sys.props(key) = value
        case None => sys.props.remove(key)

  test("import with startup configuration without changing conclusions"):
    withTrace(s"precompute_${Config.precomputeLemmas}"): prefix =>
      val output = new ByteArrayOutputStream
      var preprocessing = Option.empty[LemmaSelection.Timing]
      val timings = Console.withOut(output):
        Import.importFromPrefix(prefix, 2, failFast = true, onPreprocessing = timing => {
          assert(!output.toString.contains("Last theorem"))
          preprocessing = Some(timing)
        })
      assert(timings.forall(_.succeeded))
      val measured = preprocessing.get
      assert(measured.enabled == Config.precomputeLemmas)
      assert(measured.elapsedNanos >= 0)
      assert(measured.selectedLemmas == (if Config.precomputeLemmas then 2 else 0))
      assert(output.toString.linesIterator.count(_.startsWith("HOL_PREPROCESSING_METRICS ")) == 1)
      val last = timings.last
      if Config.reconstructionStats then
        assert(last.uniqueSteps.contains(4))
        val replay = if !Config.precomputeLemmas && Config.stepCacheCapacity == 1 && Config.stepCacheGenerations <= 1 then 2 else 0
        assert(last.recomputedSteps.contains(replay))
      else
        assert(last.uniqueSteps.isEmpty && last.recomputedSteps.isEmpty)
      val line = output.toString.linesIterator.find(_.startsWith("HOL_IMPORT_METRICS ")).get
      val metrics = ujson.read(line.stripPrefix("HOL_IMPORT_METRICS "))
      assert(metrics("precompute_lemmas").bool == Config.precomputeLemmas)
      assert(metrics("selected_lemmas").num == (if Config.precomputeLemmas then 2 else 0))
      assert(metrics("registered_lemmas").num == (if Config.precomputeLemmas then 2 else 0))
      assert(metrics("preprocessing_seconds").num == measured.elapsedSeconds)

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
      assert(timings.map(_.cacheHits) == Vector(0, 2, 1))
      assert(timings.map(_.reader.proofHeaders) == Vector(3, 1, 0))
      assert(timings.map(_.reader.proofRecords) == Vector(3, 1, 0))
      assert(timings.map(_.reader.statementRecords) == Vector(1, 1, 1))
      val firstId = timings.head.theorem.id
      assert(timings.map(_.theorem.id) == Vector(firstId, firstId + 4, firstId))
      assert(timings.forall(_.succeeded))
      assert(timings.forall(t => t.resources.cpuNanos >= -1 && t.resources.allocatedBytes >= -1 && t.resources.gcMillis >= 0))
      assert(timings.forall(t => t.elapsedNanos >= 0 && t.totalElapsedNanos >= t.elapsedNanos))
      assert(timings.sliding(2).forall(pair => pair(1).totalElapsedNanos >= pair(0).totalElapsedNanos + pair(1).elapsedNanos))
      assert(output.toString.contains("Total:"))
      assert(output.toString.contains("KiB/step"))
      assert(output.toString.contains("GC "))
      assert(output.toString.contains("reused 1 steps"))
      assert(output.toString.contains(s"Last theorem timing_shared_alias (#$firstId): OK; 0 steps"))

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
      assert(output.toString.contains("Last theorem timing_failfast_second"))
      assert(output.toString.contains("FAILED; 1 steps"))

  test("measure only requested names and their newly reconstructed dependencies"):
    withTrace("offset"): prefix =>
      val timings = Console.withOut(new ByteArrayOutputStream)(Import.importFromPrefix(prefix, 1, failFast = true, startAt = 1))
      assert(timings.size == 1)
      assert(timings.head.theorem.name == "timing_offset_second")
      assert(timings.head.steps == 3)
      assert(timings.head.totalSteps == 3)

  test("record populated typing caches and release them after successful imports"):
    withTrace("cache_success", composite = true): prefix =>
      val timings = Console.withOut(new ByteArrayOutputStream)(Import.importFromPrefix(prefix, 1, failFast = true))
      assert(timings.head.typingCacheEntries > 0)
      assert(timings.head.distinctTypes > 0)
      assert(HOLSteps.HOLProofType.cacheSize == 0)
      assert(Import.Transformers.conversionCacheSize == 0)

  test("release typing caches after failed imports"):
    withTrace("cache_failure", mismatch = true, composite = true): prefix =>
      Console.withOut(new ByteArrayOutputStream):
        assertThrows[Import.FailedTheoremException](Import.importFromPrefix(prefix, 2, failFast = true))
      assert(HOLSteps.HOLProofType.cacheSize == 0)
      assert(Import.Transformers.conversionCacheSize == 0)
