package lisa.automation.TableauBench

import java.io.File

/**
 * Quick scan: run a batch of SYN+1 problems with a short timeout to find failures.
 * Usage:
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.QuickScan"
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.QuickScan 0.00"       # only rating 0.00
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.QuickScan 0.00 0.10"  # rating 0.00 to 0.10
 */
object QuickScan {
  def main(args: Array[String]): Unit = {
    lisa.automation.Tableau.debug = false
    val minRating = if args.length > 0 then args(0).toDouble else 0.0
    val maxRating = if args.length > 1 then args(1).toDouble else 0.20
    val timeout = if args.length > 2 then args(2).toLong else 15000L

    val repoRoot = {
      val startDir = new File(sys.props.getOrElse("user.dir", "."))
      Iterator.iterate(startDir)(_.getParentFile)
        .takeWhile(_ != null)
        .find(d => new File(d, "build.sbt").exists())
        .getOrElse(startDir)
    }

    val synDir = new File(repoRoot, "tptp-pure-fol/SYN")
    val files = synDir.listFiles().filter(_.getName.endsWith("+1.p")).sortBy(_.getName)

    val ratingPattern = """% Rating\s*:\s*(\S+)""".r
    val alcPattern = """ALC, N=""".r  // Skip ALC problems (heavy branching, need different approach)

    var solved = 0
    var failed = 0
    var skipped = 0
    val failures = scala.collection.mutable.ArrayBuffer[String]()

    for (f <- files) {
      // Extract rating and check for ALC
      val src = scala.io.Source.fromFile(f)
      val lines = src.getLines().take(30).toList
      src.close()
      val rating = lines.collectFirst {
        case line if ratingPattern.findFirstMatchIn(line).isDefined =>
          ratingPattern.findFirstMatchIn(line).get.group(1).toDouble
      }.getOrElse(1.0)
      val isALC = lines.exists(line => alcPattern.findFirstIn(line).isDefined)

      if (rating >= minRating && rating <= maxRating && !isALC) {
        val result = TableauBenchmark.runBenchmark(f, timeout, verify = false)
        if (result.solved) {
          solved += 1
          println(s"[OK] ${result.solveTimeMs}ms — ${f.getName} (rating=$rating)")
        } else {
          failed += 1
          failures += f.getName
          println(s"[FAIL] ${f.getName} (rating=$rating) — ${result.error.getOrElse("no proof")}")
        }
      } else {
        skipped += 1
      }
    }

    println()
    println(s"=== QuickScan: $solved solved, $failed failed, $skipped skipped (rating $minRating-$maxRating, timeout ${timeout}ms) ===")
    if (failures.nonEmpty) {
      println(s"Failures (${failures.size}):")
      failures.foreach(f => println(s"  $f"))
    }
  }
}
