package lisa.automation.TableauBench

import java.io.File

/**
 * Scan ALL TPTP domains with configurable rating/timeout.
 * Usage:
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.DomainScan"
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.DomainScan 0.00 0.25 15000"
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.DomainScan 0.00 0.50 30000 SYN,PUZ,MGT"
 */
object DomainScan {
  case class DomainResult(domain: String, solved: Int, failed: Int, skipped: Int,
                          failures: List[(String, Double, String)], timings: List[(String, Long)])

  def main(args: Array[String]): Unit = {
    lisa.automation.Tableau.debug = false
    val minRating = if args.length > 0 then args(0).toDouble else 0.0
    val maxRating = if args.length > 1 then args(1).toDouble else 0.25
    val timeout = if args.length > 2 then args(2).toLong else 15000L
    val domainFilter = if args.length > 3 then Some(args(3).split(",").toSet) else None

    val repoRoot = {
      val startDir = new File(sys.props.getOrElse("user.dir", "."))
      Iterator.iterate(startDir)(_.getParentFile)
        .takeWhile(_ != null)
        .find(d => new File(d, "build.sbt").exists())
        .getOrElse(startDir)
    }

    val tptpDir = new File(repoRoot, "tptp-pure-fol")
    val domains = tptpDir.listFiles().filter(_.isDirectory).sortBy(_.getName)

    val ratingPattern = """% Rating\s*:\s*(\S+)""".r
    val statusPattern = """% Status\s*:\s*(\S+)""".r

    val hardDeadline = System.currentTimeMillis() + 25 * 60 * 1000L // 25 min total
    val results = scala.collection.mutable.ArrayBuffer[DomainResult]()

    for (domDir <- domains if domainFilter.forall(_.contains(domDir.getName))) {
      if (System.currentTimeMillis() > hardDeadline) {
        println(s"=== Hard deadline reached, stopping ===")
        printSummary(results.toList)
        return
      }

      val files = domDir.listFiles().filter(_.getName.endsWith(".p")).sortBy(_.getName)
      var solved = 0
      var failed = 0
      var skipped = 0
      val failures = scala.collection.mutable.ArrayBuffer[(String, Double, String)]()
      val timings = scala.collection.mutable.ArrayBuffer[(String, Long)]()

      for (f <- files) {
        if (System.currentTimeMillis() > hardDeadline) {
          results += DomainResult(domDir.getName, solved, failed, skipped, failures.toList, timings.toList)
          printSummary(results.toList)
          return
        }

        val src = scala.io.Source.fromFile(f)
        val lines = src.getLines().take(30).toList
        src.close()

        val rating = lines.collectFirst {
          case line if ratingPattern.findFirstMatchIn(line).isDefined =>
            ratingPattern.findFirstMatchIn(line).get.group(1).toDouble
        }.getOrElse(1.0)

        val status = lines.collectFirst {
          case line if statusPattern.findFirstMatchIn(line).isDefined =>
            statusPattern.findFirstMatchIn(line).get.group(1)
        }.getOrElse("Unknown")

        if (rating >= minRating && rating <= maxRating && status == "Theorem") {
          val result = TableauBenchmark.runBenchmark(f, timeout, verify = false)
          if (result.solved) {
            solved += 1
            timings += ((f.getName, result.solveTimeMs))
            if (result.solveTimeMs > 1000)
              println(s"[OK] ${result.solveTimeMs}ms — ${domDir.getName}/${f.getName} (r=$rating)")
          } else {
            failed += 1
            val err = result.error.getOrElse("no proof")
            failures += ((f.getName, rating, err))
            println(s"[FAIL] ${domDir.getName}/${f.getName} (r=$rating) — $err")
          }
        } else {
          skipped += 1
        }
      }

      if (solved + failed > 0)
        println(s"  ${domDir.getName}: $solved/${ solved + failed} solved (${failures.size} failed, $skipped skipped)")
      results += DomainResult(domDir.getName, solved, failed, skipped, failures.toList, timings.toList)
    }

    printSummary(results.toList)
  }

  def printSummary(results: List[DomainResult]): Unit = {
    println()
    println("=" * 70)
    println(f"${"Domain"}%-6s ${"Solved"}%7s ${"Failed"}%7s ${"Rate"}%6s ${"AvgMs"}%7s")
    println("-" * 70)
    var totalSolved = 0
    var totalFailed = 0
    for (r <- results if r.solved + r.failed > 0) {
      val rate = if r.solved + r.failed > 0 then f"${100.0 * r.solved / (r.solved + r.failed)}%.0f%%" else "N/A"
      val avgMs = if r.timings.nonEmpty then r.timings.map(_._2).sum / r.timings.size else 0L
      println(f"${r.domain}%-6s ${r.solved}%7d ${r.failed}%7d $rate%6s ${avgMs}%7d")
      totalSolved += r.solved
      totalFailed += r.failed
    }
    println("-" * 70)
    val totalRate = if totalSolved + totalFailed > 0 then f"${100.0 * totalSolved / (totalSolved + totalFailed)}%.0f%%" else "N/A"
    println(f"${"TOTAL"}%-6s ${totalSolved}%7d ${totalFailed}%7d ${totalRate}%6s")
    println("=" * 70)

    val allFailures = results.flatMap(r => r.failures.map(f => (r.domain, f._1, f._2, f._3)))
    if (allFailures.nonEmpty) {
      println(s"\nAll failures (${allFailures.size}):")
      for ((domain, file, rating, err) <- allFailures.sortBy(x => x._3: Double)) {
        val shortErr = if err.length > 50 then err.take(50) + "..." else err
        println(f"  $domain%-5s/$file%-20s r=$rating%.2f — $shortErr")
      }
    }
  }
}
