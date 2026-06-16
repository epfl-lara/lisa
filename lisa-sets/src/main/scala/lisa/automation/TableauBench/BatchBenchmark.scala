package lisa.automation.TableauBench

import java.io.{File, PrintWriter}

/**
 * Batch benchmark that surveys TPTP problems across difficulty levels.
 * Produces a summary of solve rates by domain and difficulty.
 *
 * Usage:
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.BatchBenchmark"
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.BatchBenchmark --maxPerBucket 5 --timeout 10000"
 */
object BatchBenchmark {

  def main(args: Array[String]): Unit = {
    lisa.automation.Tableau.debug = false

    val maxPerBucket = args.indexOf("--maxPerBucket") match
      case -1 => 10
      case i => args(i + 1).toInt
    val timeout = args.indexOf("--timeout") match
      case -1 => 60000L
      case i => args(i + 1).toLong

    // Find repo root
    val startDir = new File(sys.props.getOrElse("user.dir", "."))
    val repoRoot = Iterator.iterate(startDir)(_.getParentFile)
      .takeWhile(_ != null)
      .find(d => new File(d, "build.sbt").exists())
      .getOrElse(startDir)
    val tptpDir = new File(repoRoot, "tptp-pure-fol")

    // Collect all problems with ratings
    case class ProblemInfo(file: File, domain: String, name: String, rating: Double)

    val problems = tptpDir.listFiles().filter(_.isDirectory).flatMap { domainDir =>
      domainDir.listFiles().filter(_.getName.endsWith(".p")).flatMap { f =>
        val rating = extractRating(f)
        rating.map(r => ProblemInfo(f, domainDir.getName, f.getName.stripSuffix(".p"), r))
      }
    }.toSeq.sortBy(_.rating)

    // Bucket by rating ranges
    val buckets = Seq(
      (0.0, 0.0, "trivial"),
      (0.01, 0.17, "easy"),
      (0.18, 0.33, "medium-easy"),
      (0.34, 0.50, "medium"),
      (0.51, 0.67, "medium-hard"),
      (0.68, 0.83, "hard"),
      (0.84, 1.00, "very-hard")
    )

    val results = scala.collection.mutable.ArrayBuffer[(ProblemInfo, TableauBenchmark.BenchmarkResult)]()

    for ((lo, hi, label) <- buckets) {
      val inBucket = problems.filter(p => p.rating >= lo && p.rating <= hi)
      // Sample evenly across domains
      val sampled = if (inBucket.size <= maxPerBucket) inBucket
        else {
          val byDomain = inBucket.groupBy(_.domain)
          val perDomain = math.max(1, maxPerBucket / byDomain.size)
          byDomain.values.flatMap(_.take(perDomain)).toSeq.take(maxPerBucket)
        }

      println(s"\n=== Bucket: $label [$lo, $hi] — ${inBucket.size} total, testing ${sampled.size} ===")
      for (p <- sampled) {
        val result = TableauBenchmark.runBenchmark(p.file, timeout, verify = true)
        results += ((p, result))
        val status = if (result.solved && result.proofValid.contains(true)) "VALID"
          else if (result.solved && result.proofValid.contains(false)) "INVALID"
          else if (result.solved) "SOLVED"
          else "FAIL"
        println(f"  [$status%7s] ${result.solveTimeMs}%6dms  r=${p.rating}%.2f  ${p.domain}/${p.name}")
      }
    }

    // Summary
    println("\n=== SUMMARY ===")
    for ((lo, hi, label) <- buckets) {
      val bucketResults = results.filter { case (p, _) => p.rating >= lo && p.rating <= hi }
      val valid = bucketResults.count { case (_, r) => r.solved && r.proofValid.contains(true) }
      val invalid = bucketResults.count { case (_, r) => r.solved && r.proofValid.contains(false) }
      val fail = bucketResults.count { case (_, r) => !r.solved }
      val total = bucketResults.size
      if (total > 0) {
        println(f"$label%-14s: $valid%3d/$total%3d valid, $invalid invalid, $fail fail")
      }
    }

    // Write CSV
    val csvFile = new File(repoRoot, "lisa-sets/src/main/scala/lisa/automation/TableauBench/batch_results.csv")
    val pw = new PrintWriter(csvFile)
    pw.println("domain,problem,rating,solved,proofValid,solveTimeMs,proofSteps,error")
    for ((p, r) <- results) {
      val validStr = r.proofValid.map(_.toString).getOrElse("")
      val errStr = r.error.map(e => "\"" + e.replace("\"", "'") + "\"").getOrElse("")
      pw.println(s"${p.domain},${p.name},${p.rating},${r.solved},$validStr,${r.solveTimeMs},${r.proofSteps.getOrElse("")},$errStr")
    }
    pw.close()
    println(s"\nResults written to ${csvFile.getPath}")
  }

  def extractRating(f: File): Option[Double] = {
    val source = scala.io.Source.fromFile(f)
    try {
      source.getLines().find(_.contains("% Rating")).flatMap { line =>
        // Format: "% Rating   : 0.33 v2.5.0, ..."
        val afterColon = line.split(":")(1).trim
        val firstRating = afterColon.split("\\s+")(0)
        try Some(firstRating.toDouble) catch case _: Exception => None
      }
    } finally source.close()
  }
}
