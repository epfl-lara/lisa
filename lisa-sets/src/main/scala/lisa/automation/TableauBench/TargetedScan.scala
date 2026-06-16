package lisa.automation.TableauBench

import java.io.File

/**
 * Targeted scan of self-contained easy problems across multiple domains.
 * Reports which specific problems fail, sorted by domain.
 * Usage: runMain lisa.automation.TableauBench.TargetedScan [timeoutMs]
 */
object TargetedScan {
  def main(args: Array[String]): Unit = {
    val timeoutMs = if args.length > 0 then args(0).toLong else 10000L
    val maxRating = if args.length > 1 then args(1).toDouble else 0.15

    val baseDir = {
      val direct = new File("tptp-pure-fol")
      if (direct.exists()) direct
      else {
        val parent = new File(sys.props.getOrElse("user.dir", ".")).getParentFile
        if (parent != null) new File(parent, "tptp-pure-fol")
        else direct
      }
    }
    if (!baseDir.exists()) {
      println(s"ERROR: $baseDir not found")
      sys.exit(1)
    }

    // Scan all domains for self-contained (no includes) easy Theorem problems
    val domains = baseDir.listFiles().filter(_.isDirectory).map(_.getName).sorted
    var totalPassed = 0
    var totalFailed = 0
    val failedProblems = scala.collection.mutable.ArrayBuffer[(String, String, Long)]() // (domain/file, error, timeMs)

    for (domain <- domains) {
      val domainDir = new File(baseDir, domain)
      val problems = domainDir.listFiles().filter(f => f.getName.endsWith(".p") && f.getName.contains("+")).sortBy(_.getName)
      
      var passed = 0
      var failed = 0
      var skipped = 0

      for (pFile <- problems) {
        // Check rating and self-containedness
        val meta = extractMeta(pFile)
        if (meta._1 > maxRating || meta._2 != "Theorem" || meta._3) {
          skipped += 1
        } else {
          val result = TableauBenchmark.runBenchmark(pFile, timeoutMs, verify = false)
          if (result.solved) {
            passed += 1
          } else {
            failed += 1
            failedProblems += ((s"$domain/${pFile.getName}", result.error.getOrElse("unknown"), result.solveTimeMs))
          }
        }
      }

      totalPassed += passed
      totalFailed += failed
      val total = passed + failed
      if (total > 0) {
        println(f"$domain%-6s $passed%3d/$total%3d passed (${if total > 0 then passed * 100 / total else 0}%3d%%)")
        System.out.flush()
      }
    }

    println()
    println(f"=== TOTAL: $totalPassed/${totalPassed + totalFailed} passed (${if totalPassed + totalFailed > 0 then totalPassed * 100 / (totalPassed + totalFailed) else 0}%%) ===")
    if (failedProblems.nonEmpty) {
      println(s"\nFailed problems (${failedProblems.size}):")
      for ((name, error, timeMs) <- failedProblems.sortBy(_._1)) {
        println(f"  $name%-30s ${timeMs}%6dms  $error")
      }
    }
  }

  private def extractMeta(file: File): (Double, String, Boolean) = {
    val src = scala.io.Source.fromFile(file)
    try {
      var rating = 1.0
      var status = "Unknown"
      var hasInclude = false
      for (line <- src.getLines().take(40)) {
        if (line.startsWith("% Rating")) {
          val parts = line.split(":")
          if (parts.length >= 2) {
            try { rating = parts(1).trim.split(" ")(0).trim.toDouble }
            catch { case _: NumberFormatException => () }
          }
        }
        if (line.startsWith("% Status")) {
          val parts = line.split(":")
          if (parts.length >= 2) status = parts(1).trim
        }
        if (line.startsWith("include(")) hasInclude = true
      }
      (rating, status, hasInclude)
    } finally { src.close() }
  }
}
