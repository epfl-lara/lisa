package lisa.hol

import java.nio.file.Files
import org.scalatest.funsuite.AnyFunSuite

class ImportStatisticsSuite extends AnyFunSuite:
  test("filter step shapes by named target, allocation and selected rule without evaluating rejected metadata"):
    import lisa.utils.prooflib.{BasicStep, Library}
    import lisa.utils.fol.FOL.{_, given}
    given Library = new Library
    val p = variable[Prop]
    val directory = Files.createTempDirectory("lisa-filtered-statistics")
    val output = directory.resolve("steps.csv")
    val statistics = new ImportStatistics(stepOutput = Some(output), stepFromTheorem = 100, stepRules = Set("INST"))
    try
      statistics.begin(99)
      statistics.measureRule("INST", 7, sys.error("early metadata"), sys.error("early size"))(BasicStep.Restate(p |- p))
      statistics.begin(100)
      statistics.measureRule("EQ_MP", 8, sys.error("unselected metadata"), 0)(BasicStep.Restate(p |- p))
      statistics.measureRule("INST", 9, Nil, 1)(BasicStep.Restate(p |- p))
      statistics.finish(100, "selected")
      val rows = Files.readString(output).linesIterator.toVector
      assert(rows.size == 2)
      assert(rows.last.split(",").take(2).toSeq == Seq("9", "INST"))
      assert(rows.last.split(",").last == "100")
    finally statistics.close()
    val filtered = directory.resolve("filtered.csv")
    val expensive = new ImportStatistics(stepOutput = Some(filtered), stepMinBytes = Long.MaxValue)
    try
      expensive.measureRule("EQ_MP", 10, sys.error("below threshold"), sys.error("below threshold"))(BasicStep.Restate(p |- p))
      expensive.finish(100, "filtered")
      assert(Files.readString(filtered).linesIterator.size == 1)
    finally
      expensive.close()
      Files.deleteIfExists(output)
      Files.deleteIfExists(filtered)
      Files.deleteIfExists(directory)

  test("reject negative profiling limits before creating output"):
    assertThrows[IllegalArgumentException](new ImportStatistics(stepMinBytes = -1))
    assertThrows[IllegalArgumentException](new ImportStatistics(stepFromTheorem = -1))

  test("record the largest exclusive allocation and its step, including throwing frames"):
    val directory = Files.createTempDirectory("lisa-allocation-max")
    val output = directory.resolve("costs.csv")
    val statistics = new ImportStatistics(Some(output))
    try
      statistics.measure("parent", 1):
        statistics.measure("child", 2)(new Array[Byte](1000000))
      intercept[IllegalArgumentException]:
        statistics.measure("child", 3):
          val bytes = new Array[Byte](2000000)
          throw new IllegalArgumentException(bytes.length.toString)
      statistics.finish(4, "allocation")
      val rows = Files.readString(output).linesIterator.drop(1).map(_.split(",")).map(r => r(2) -> r).toMap
      if ImportStatistics.sample().allocatedBytes >= 0 then
        assert(rows("child")(10).toLong >= 2000000L)
        assert(rows("child")(11) == "3")
        assert(rows("parent")(10).toLong < rows("child")(10).toLong)
      else assert(rows.values.forall(r => r(10) == "-1" && r(11) == "-1"))
    finally
      statistics.close()
      Files.deleteIfExists(output)
      Files.deleteIfExists(directory)

  test("disabled step profiling does not evaluate premise metadata"):
    import lisa.utils.prooflib.{BasicStep, Library}
    import lisa.utils.fol.FOL.{_, given}
    given Library = new Library
    val p = variable[Prop]
    val statistics = new ImportStatistics
    try
      val result = statistics.measureRule("EQ_MP", 1, sys.error("premises evaluated"), sys.error("cache evaluated")):
        BasicStep.Restate(p |- p)
      assert(result.isValid)
    finally statistics.close()

  test("stream selected rule sizes and preserve failures without fabricated success rows"):
    import lisa.utils.prooflib.{BasicStep, Library}
    import lisa.utils.fol.FOL.{_, given}
    given Library = new Library
    val p = variable[Prop]
    val directory = Files.createTempDirectory("lisa-step-statistics")
    val output = directory.resolve("steps.csv")
    val statistics = new ImportStatistics(stepOutput = Some(output))
    try
      val premise = BasicStep.Restate(p |- p).kernel
      assert(statistics.measureRule("EQ_MP", 7, Seq(premise), 12)(BasicStep.Restate(p |- p)).isValid)
      assertThrows[IllegalArgumentException]:
        statistics.measureRule("MK_COMB", 8, Nil, 12)(throw new IllegalArgumentException("failure"))
      statistics.measureRule("REFL", 9, sys.error("unselected"), 12)(BasicStep.Restate(p |- p))
      statistics.finish(9, "test")
      val lines = Files.readString(output).linesIterator.toVector
      assert(lines.size == 2)
      val row = lines(1).split(",")
      assert(row.take(2).toSeq == Seq("7", "EQ_MP"))
      assert(row(5) == "12")
      assert(row.slice(6, 14).toSeq == Seq("2", "1", "2", "1", "2", "1", "2", "1"))
    finally
      statistics.close()
      Files.deleteIfExists(output)
      Files.deleteIfExists(directory)

  test("resource deltas preserve unavailable counters"):
    import ImportStatistics.Sample
    assert(Sample(30, 70, 9) - Sample(10, 20, 3) == Sample(20, 50, 6))
    assert(Sample(-1, -1, 9) - Sample(-1, -1, 3) == Sample(-1, -1, 6))

  test("disabled statistics preserve results and exceptions"):
    val statistics = new ImportStatistics
    try
      assert(statistics.measure("REFL", 0)(42) == 42)
      val failure = new IllegalArgumentException("test")
      assert(intercept[IllegalArgumentException](statistics.measure("INST", 1)(throw failure)) eq failure)
      statistics.finish(1, "test")
    finally statistics.close()

  test("CSV costs exclude nested phases and retain failures"):
    val directory = Files.createTempDirectory("lisa-import-statistics")
    val output = directory.resolve("rules.csv")
    val statistics = new ImportStatistics(Some(output))
    try
      val started = System.nanoTime()
      statistics.measure("parent", 3):
        statistics.measure("child", 2):
          (1 to 1000).sum
      val elapsed = System.nanoTime() - started
      statistics.finish(3, "nested")
      val rows = Files.readString(output).linesIterator.drop(1).map(_.split(",")).toVector
      assert(rows.map(_(2)).toSet == Set("parent", "child"))
      assert(rows.forall(row => row(3) == "1" && row(4) == "0"))
      assert(rows.map(_(5).toLong).sum <= elapsed)

      intercept[IllegalArgumentException]:
        statistics.measure("INST", 4)(throw new IllegalArgumentException("test"))
      statistics.finish(4, "failure")
      val last = Files.readString(output).linesIterator.toVector.last.split(",")
      assert(last(2) == "INST" && last(3) == "1" && last(4) == "1")
      assert(last(9) == "4")
    finally
      statistics.close()
      Files.deleteIfExists(output)
      Files.deleteIfExists(directory)

  test("existing statistics files are not overwritten"):
    val output = Files.createTempFile("lisa-existing-statistics", ".csv")
    try
      Files.writeString(output, "keep")
      intercept[java.nio.file.FileAlreadyExistsException](new ImportStatistics(Some(output)))
      assert(Files.readString(output) == "keep")
    finally Files.deleteIfExists(output)
