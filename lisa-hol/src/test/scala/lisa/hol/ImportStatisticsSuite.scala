package lisa.hol

import java.nio.file.Files
import org.scalatest.funsuite.AnyFunSuite

class ImportStatisticsSuite extends AnyFunSuite:
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
