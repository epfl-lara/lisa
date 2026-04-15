package lisa.automation.TableauBench

import java.io.File

/**
 * Scan all TPTP domains for FOF (+1) problems and test them.
 * Usage:
 *   sbt "lisa-sets/runMain lisa.automation.TableauBench.DomainScan"
 *   sbt "lisa-sets/runMain lisa.automation.TableauBench.DomainScan 10000"  # custom timeout
 */
object DomainScan {
  def main(args: Array[String]): Unit = {
    lisa.automation.Tableau.debug = false
    val timeout = if args.length > 0 then args(0).toLong else 15000L

    val repoRoot = {
      val startDir = new File(sys.props.getOrElse("user.dir", "."))
      Iterator.iterate(startDir)(_.getParentFile)
        .takeWhile(_ != null)
        .find(d => new File(d, "build.sbt").exists())
        .getOrElse(startDir)
    }

    val tptpDir = new File(repoRoot, "tptp-pure-fol")
    val domains = tptpDir.listFiles().filter(_.isDirectory).sortBy(_.getName)

    var totalSolved = 0
    var totalFailed = 0
    var totalSkipped = 0

    for (domain <- domains) {
      if domain.getName == "SYN" then
        println(s"  [SKIP] SYN domain (use QuickScan instead)")
      else
        // Get FOF problems (+1 and plain .p without -N suffix)  
        val files = domain.listFiles().filter { f =>
          f.getName.endsWith(".p") && (f.getName.contains("+1") || f.getName.contains("+2") || f.getName.contains("+3"))
        }.sortBy(_.getName)

        if files.isEmpty then
          println(s"  [SKIP] ${domain.getName}: no FOF problems")
          totalSkipped += files.length
        else
          var solved = 0
          var failed = 0
          for (file <- files) {
            try {
              val result = TableauBenchmark.runBenchmark(
                problemFile = file,
                timeoutMs = timeout,
                verify = true
              )
              if result.solved then
                solved += 1
                println(s"  [OK] ${result.solveTimeMs}ms — ${file.getName}")
              else
                failed += 1
                val reason = result.error.getOrElse(s"Timeout after ${timeout}ms")
                println(s"  [FAIL] ${file.getName} — $reason")
            } catch {
              case e: Exception =>
                failed += 1
                println(s"  [FAIL] ${file.getName} — ${e.getClass.getSimpleName}: ${e.getMessage.take(80)}")
            }
          }
          println(s"  ${domain.getName}: $solved/${files.length} solved")
          totalSolved += solved
          totalFailed += failed
    }

    println(s"\n=== Domain Scan: $totalSolved solved, $totalFailed failed (timeout ${timeout}ms) ===")
  }
}
