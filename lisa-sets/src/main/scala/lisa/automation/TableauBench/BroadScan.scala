package lisa.automation.TableauBench

import java.io.File

/**
 * Broad scan across all TPTP domains with configurable rating filter.
 * Usage: runMain lisa.automation.TableauBench.BroadScan [maxRating] [timeoutMs]
 * Defaults: maxRating=0.15, timeoutMs=8000
 */
object BroadScan {
  def main(args: Array[String]): Unit = {
    val maxRating = if args.length > 0 then args(0).toDouble else 0.15
    val timeoutMs = if args.length > 1 then args(1).toLong else 8000L

    val baseDir = {
      val direct = new File("tptp-pure-fol")
      if (direct.exists()) direct
      else {
        // sbt fork may set cwd to subproject; try parent
        val parent = new File(sys.props.getOrElse("user.dir", ".")).getParentFile
        if (parent != null) new File(parent, "tptp-pure-fol")
        else direct
      }
    }
    if (!baseDir.exists()) {
      println(s"ERROR: $baseDir not found")
      sys.exit(1)
    }

    val domains = baseDir.listFiles().filter(_.isDirectory).map(_.getName).sorted
    var totalPassed = 0
    var totalFailed = 0
    var totalSkipped = 0
    val globalStartMs = System.currentTimeMillis()
    val globalTimeLimitMs = 15 * 60 * 1000L // 15 minutes max
    val domainTimeLimitMs = 90 * 1000L // 90s per domain max

    for (domain <- domains if System.currentTimeMillis() - globalStartMs < globalTimeLimitMs) {
      val domainDir = new File(baseDir, domain)
      val problems = domainDir.listFiles().filter(_.getName.endsWith(".p")).sortBy(_.getName)
      val domainStartMs = System.currentTimeMillis()
      
      var passed = 0
      var failed = 0
      var skipped = 0

      for (pFile <- problems if System.currentTimeMillis() - domainStartMs < domainTimeLimitMs) {
        val name = pFile.getName
        // Skip CNF problems — TPTP convention: '+' = FOF/TFF, '-' = CNF/clause-based
        val isCNF = !name.contains("+")
        val rating = extractRating(pFile)
        if (isCNF || rating > maxRating) {
          skipped += 1
        } else {
          val result = TableauBenchmark.runBenchmark(pFile, timeoutMs, verify = false)
          if (result.solved) passed += 1 else failed += 1
        }
      }

      totalPassed += passed
      totalFailed += failed
      totalSkipped += skipped
      val total = passed + failed
      if (total > 0) {
        println(f"$domain%-6s $passed%3d/$total%3d passed (${if total > 0 then passed * 100 / total else 0}%3d%%), $skipped skipped")
      }
    }

    println()
    println(f"=== TOTAL: $totalPassed/${ totalPassed + totalFailed } passed (${if totalPassed + totalFailed > 0 then totalPassed * 100 / (totalPassed + totalFailed) else 0}%%), $totalSkipped skipped (r>$maxRating) ===")
  }

  private def extractRating(file: File): Double = {
    val src = scala.io.Source.fromFile(file)
    try {
      val lines = src.getLines().take(30)
      for (line <- lines) {
        if (line.startsWith("% Rating")) {
          val parts = line.split(":")
          if (parts.length >= 2) {
            val ratingStr = parts(1).trim.split(" ")(0).trim
            try { return ratingStr.toDouble }
            catch { case _: NumberFormatException => () }
          }
        }
      }
      1.0
    } finally { src.close() }
  }
}
