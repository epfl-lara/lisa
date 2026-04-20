package lisa.automation.TableauBench

import java.io.File

/**
 * Run TableauBenchmark on an explicit list of problems and print a compact summary.
 *
 * Usage:
 *   runMain lisa.automation.TableauBench.SelectedProblemsBench [timeoutMs] <problem1> <problem2> ...
 *
 * If the first argument is numeric it is used as the timeout in milliseconds,
 * otherwise the default timeout is 10000 ms.
 */
object SelectedProblemsBench {

  def main(args: Array[String]): Unit = {
    lisa.automation.Tableau.debug = false

    val (timeoutMs, problemArgs) =
      if args.nonEmpty && args(0).forall(_.isDigit) then (args(0).toLong, args.drop(1).toSeq)
      else (10000L, args.toSeq)

    if problemArgs.isEmpty then {
      System.err.println("Usage: runMain lisa.automation.TableauBench.SelectedProblemsBench [timeoutMs] <problem1> <problem2> ...")
      return
    }

    val repoRoot = {
      val startDir = new File(sys.props.getOrElse("user.dir", "."))
      Iterator.iterate(startDir)(_.getParentFile)
        .takeWhile(_ != null)
        .find(d => new File(d, "build.sbt").exists())
        .getOrElse(startDir)
    }

    val problems = problemArgs.map { p =>
      val direct = new File(p)
      if direct.isAbsolute || direct.exists() then direct else new File(repoRoot, p)
    }

    println(s"Benchmarking ${problems.size} selected problems (timeout=${timeoutMs}ms)")
    println()

    var solved = 0
    var failed = 0

    for ((file, idx) <- problems.zipWithIndex) {
      val result = TableauBenchmark.runBenchmark(file, timeoutMs = timeoutMs, verify = false)
      val status = if result.solved then { solved += 1; "PASS" } else { failed += 1; "FAIL" }
      val problemLabel = problemArgs(idx)
      val errorSuffix = if result.solved then "" else s" (${result.error.getOrElse("?")})"
      println(f"[$status] ${result.solveTimeMs}%5dms  $problemLabel$errorSuffix")
    }

    println()
    println(s"=== Selected set: $solved/${solved + failed} solved ===")
  }
}