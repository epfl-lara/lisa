package lisa.automation.TableauBench

import java.io.File

/**
 * Scan easy problems (rating <= 0.20) across all domains to find failures.
 * Usage: runMain lisa.automation.TableauBench.EasyScan [timeoutMs] [maxPerDomain]
 */
object EasyScan {
  def main(args: Array[String]): Unit = {
    lisa.automation.Tableau.debug = false
    val timeoutMs = if args.length > 0 then args(0).toLong else 10000L
    val maxPerDomain = if args.length > 1 then args(1).toInt else 10
    val maxRating = if args.length > 2 then args(2).toDouble else 0.20

    val repoRoot = {
      val startDir = new File(sys.props.getOrElse("user.dir", "."))
      Iterator.iterate(startDir)(_.getParentFile)
        .takeWhile(_ != null)
        .find(d => new File(d, "build.sbt").exists())
        .getOrElse(startDir)
    }

    val tptpDir = new File(repoRoot, "tptp-pure-fol")
    val ratingPattern = """% Rating\s*:\s*(\S+)""".r
    val statusPattern = """% Status\s*:\s*(\S+)""".r

    var totalSolved = 0
    var totalFailed = 0
    val failures = scala.collection.mutable.ArrayBuffer[(String, String)]()

    for (domain <- tptpDir.listFiles().filter(_.isDirectory).sortBy(_.getName)) {
      val files = domain.listFiles().filter(_.getName.endsWith(".p")).sortBy(_.getName)
      var domainProbs = scala.collection.mutable.ArrayBuffer[(File, Double)]()

      for (f <- files) {
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
        if (status == "Theorem" && rating <= maxRating) {
          domainProbs += ((f, rating))
        }
      }

      // Sort by rating (easiest first) and take up to maxPerDomain
      val selected = domainProbs.sortBy(_._2).take(maxPerDomain)
      if (selected.nonEmpty) {
        var domSolved = 0
        var domFailed = 0
        for ((f, rating) <- selected) {
          val result = TableauBenchmark.runBenchmark(f, timeoutMs, verify = false)
          if (result.solved) {
            domSolved += 1
            totalSolved += 1
          } else {
            domFailed += 1
            totalFailed += 1
            failures += ((s"${domain.getName}/${f.getName}", result.error.getOrElse("?")))
          }
        }
        val mark = if domFailed == 0 then "OK" else "!!"
        System.err.println(f"[$mark] ${domain.getName}%4s: $domSolved%2d/${selected.size}%2d passed (of ${domainProbs.size}%3d easy probs)")
        System.err.flush()
      }
    }

    System.err.println(s"\n=== TOTAL: $totalSolved/${totalSolved + totalFailed} passed ===")
    if (failures.nonEmpty) {
      System.err.println(s"\nFailing problems (${failures.size}):")
      for ((p, err) <- failures.sortBy(_._1)) {
        System.err.println(s"  $p — $err")
      }
    }
    System.err.flush()
  }
}
