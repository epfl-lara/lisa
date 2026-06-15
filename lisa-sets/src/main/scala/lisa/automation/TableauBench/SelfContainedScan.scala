package lisa.automation.TableauBench

import java.io.File
import scala.io.Source

/**
 * Scans self-contained (no includes) Theorem problems across all domains.
 * Usage: runMain lisa.automation.TableauBench.SelfContainedScan [timeoutMs] [maxRating] [maxPerDomain]
 * Default: 10000ms timeout, 0.20 max rating, 10 per domain
 */
object SelfContainedScan {
  def main(args: Array[String]): Unit = {
    val timeoutMs = if args.length > 0 then args(0).toLong else 10000L
    val maxRating = if args.length > 1 then args(1).toDouble else 0.20
    val maxPerDomain = if args.length > 2 then args(2).toInt else 10

    val repoRoot = {
      val startDir = new File(sys.props.getOrElse("user.dir", "."))
      Iterator.iterate(startDir)(_.getParentFile)
        .takeWhile(_ != null)
        .find(d => new File(d, "build.sbt").exists())
        .getOrElse(startDir)
    }
    val baseDir = new File(repoRoot, "tptp-pure-fol")
    if (!baseDir.isDirectory) { println("ERROR: tptp-pure-fol not found"); return }

    // Collect all candidate problems
    case class Problem(file: File, domain: String, rating: Double)
    val allProblems = scala.collection.mutable.ListBuffer.empty[Problem]

    for (domDir <- baseDir.listFiles().filter(_.isDirectory).sortBy(_.getName)) {
      val domain = domDir.getName
      for (pFile <- domDir.listFiles().filter(_.getName.endsWith(".p")).sortBy(_.getName)) {
        val content = Source.fromFile(pFile).mkString
        // Skip problems with includes
        if (!content.contains("include(")) {
          val ratingMatch = """% Rating\s*:\s*([\d.]+)""".r.findFirstMatchIn(content)
          val statusMatch = """% Status\s*:\s*(\w+)""".r.findFirstMatchIn(content)
          val rating = ratingMatch.map(_.group(1).toDouble).getOrElse(1.0)
          val status = statusMatch.map(_.group(1)).getOrElse("Unknown")
          if (status == "Theorem" && rating <= maxRating) {
            allProblems += Problem(pFile, domain, rating)
          }
        }
      }
    }

    // Select up to maxPerDomain per domain, sorted by rating (easiest first)
    val selected = allProblems
      .groupBy(_.domain)
      .toSeq.sortBy(_._1)
      .flatMap { case (domain, probs) =>
        probs.sortBy(_.rating).take(maxPerDomain)
      }

    println(s"Testing ${selected.size} self-contained Theorem problems (timeout=${timeoutMs}ms, maxRating=$maxRating, maxPerDomain=$maxPerDomain)")
    println()

    var passed = 0
    var failed = 0
    var timeouts = 0
    var noProof = 0
    val failures = scala.collection.mutable.ListBuffer.empty[String]
    val domainStats = scala.collection.mutable.Map.empty[String, (Int, Int)] // domain -> (pass, total)

    for (prob <- selected) {
      val relPath = s"tptp-pure-fol/${prob.domain}/${prob.file.getName}"
      val result = TableauBenchmark.runBenchmark(
        problemFile = prob.file,
        timeoutMs = timeoutMs,
        verify = false
      )
      val (dp, dt) = domainStats.getOrElseUpdate(prob.domain, (0, 0))
      if (result.solved) {
        passed += 1
        domainStats(prob.domain) = (dp + 1, dt + 1)
        println(f"  [PASS] ${result.solveTimeMs}%5dms  r=${prob.rating}%.2f  $relPath")
      } else {
        failed += 1
        domainStats(prob.domain) = (dp, dt + 1)
        val reason = result.error.getOrElse("Unknown")
        if (reason.contains("Timeout")) timeouts += 1
        else noProof += 1
        failures += f"  [FAIL] r=${prob.rating}%.2f  $relPath  ($reason)"
        println(f"  [FAIL] ${result.solveTimeMs}%5dms  r=${prob.rating}%.2f  $relPath  ($reason)")
      }
    }

    println()
    println(s"=== Results: $passed passed, $failed failed ($timeouts timeouts, $noProof no-proof) out of ${selected.size} ===")
    println()
    println("Domain breakdown:")
    for ((domain, (p, t)) <- domainStats.toSeq.sortBy(_._1)) {
      println(f"  $domain%-5s: $p%2d / $t%2d")
    }
    if (failures.nonEmpty) {
      println()
      println("Failures:")
      failures.foreach(println)
    }
  }
}
