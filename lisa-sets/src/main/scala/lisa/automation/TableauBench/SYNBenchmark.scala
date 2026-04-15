package lisa.automation.TableauBench

import java.io.File

/**
 * Run all SYN+1.p problems and report solve rate.
 * Usage:
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.SYNBenchmark [timeout_ms]"
 */
object SYNBenchmark {
  def main(args: Array[String]): Unit = {
    val timeout = if args.length > 0 then args(0).toLong else 30000L
    lisa.automation.Tableau.debug = false

    val startDir = new File(sys.props.getOrElse("user.dir", "."))
    val repoRoot = Iterator.iterate(startDir)(_.getParentFile)
      .takeWhile(_ != null)
      .find(d => new File(d, "build.sbt").exists())
      .getOrElse(startDir)

    val dir = new File(repoRoot, "tptp-pure-fol/SYN")
    val files = dir.listFiles().filter(_.getName.endsWith("+1.p")).sortBy(_.getName)
    println(s"Running ${files.length} SYN+1 problems, timeout=${timeout}ms")

    var solved = 0
    var invalid = 0
    var failed = 0
    val invalidList = scala.collection.mutable.ArrayBuffer[String]()
    val failedList = scala.collection.mutable.ArrayBuffer[String]()

    for ((f, i) <- files.zipWithIndex) {
      val result = TableauBenchmark.runBenchmark(f, timeout, verify = true)
      if result.solved && result.proofValid.contains(true) then solved += 1
      else if result.solved && result.proofValid.contains(false) then {
        invalid += 1; invalidList += f.getName
        println(s"  [INVALID] ${f.getName} — ${result.solveTimeMs}ms")
      }
      else { failed += 1; failedList += f.getName }
      if ((i + 1) % 40 == 0 || i + 1 == files.length)
        println(s"  Progress: ${i+1}/${files.length} | solved=$solved invalid=$invalid failed=$failed")
    }

    println(s"\n=== SYN+1: $solved/${files.length} solved ($invalid invalid) ===")
    if invalidList.nonEmpty then println(s"Invalid: ${invalidList.mkString(", ")}")
  }
}
