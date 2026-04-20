package lisa.automation.TableauBench

import java.io.File

/**
 * Correctness baseline: a fixed set of TPTP problems that must always produce
 * kernel-verified proofs. Run after every Tableau.scala change.
 *
 * Usage:
 *   sbtn "lisa-sets/runMain lisa.automation.TableauBench.CorrectnessBaseline"
 */
object CorrectnessBaseline {

  /** (relative path from repo root, expected max time in ms) */
  val problems: Seq[(String, Long)] = Seq(
    // Pelletier problems (rating 0.00–0.17)
    ("tptp-pure-fol/SYN/SYN048+1.p", 2000),   // Pelletier 18
    ("tptp-pure-fol/SYN/SYN054+1.p", 2000),   // Pelletier 24
    ("tptp-pure-fol/SYN/SYN056+1.p", 2000),   // Pelletier 26
    ("tptp-pure-fol/SYN/SYN057+1.p", 2000),   // Pelletier 27
    ("tptp-pure-fol/SYN/SYN058+1.p", 2000),   // Pelletier 28
    ("tptp-pure-fol/SYN/SYN059+1.p", 2000),   // Pelletier 29
    ("tptp-pure-fol/SYN/SYN060+1.p", 2000),   // Pelletier 30
    ("tptp-pure-fol/SYN/SYN061+1.p", 2000),   // Pelletier 31
    ("tptp-pure-fol/SYN/SYN062+1.p", 2000),   // Pelletier 32
    ("tptp-pure-fol/SYN/SYN063+1.p", 2000),   // Pelletier 33
    ("tptp-pure-fol/SYN/SYN064+1.p", 2000),   // Pelletier 35
    ("tptp-pure-fol/SYN/SYN065+1.p", 2000),   // Pelletier 36
    ("tptp-pure-fol/SYN/SYN066+1.p", 2000),   // Pelletier 37 (solved via backtracking)
    ("tptp-pure-fol/SYN/SYN068+1.p", 2000),   // Pelletier 44
    ("tptp-pure-fol/SYN/SYN070+1.p", 2000),   // Pelletier 46
    ("tptp-pure-fol/SYN/SYN073+1.p", 2000),   // Pelletier 50
    ("tptp-pure-fol/SYN/SYN079+1.p", 2000),   // Pelletier 57
    ("tptp-pure-fol/SYN/SYN081+1.p", 2000),   // Pelletier 59
    ("tptp-pure-fol/SYN/SYN082+1.p", 2000),   // Pelletier 60
    ("tptp-pure-fol/SYN/SYN084+1.p", 2000),   // Pelletier 62
    // Church problems (rating 0.00–0.50)
    ("tptp-pure-fol/SYN/SYN315+1.p", 2000),   // Church 46.2(1)
    ("tptp-pure-fol/SYN/SYN317+1.p", 2000),   // Church 46.2(3)
    ("tptp-pure-fol/SYN/SYN318+1.p", 2000),   // Church 46.2(4)
    ("tptp-pure-fol/SYN/SYN319+1.p", 2000),   // Church 46.2(5)
    ("tptp-pure-fol/SYN/SYN321+1.p", 2000),   // Church 46.3(2) — previously INVALID
    ("tptp-pure-fol/SYN/SYN323+1.p", 2000),   // Church 46.4(2) — previously INVALID
    ("tptp-pure-fol/SYN/SYN327+1.p", 2000),   // Church 46.12(2)
    ("tptp-pure-fol/SYN/SYN333+1.p", 2000),   // Church 46.14(5)
    ("tptp-pure-fol/SYN/SYN338+1.p", 2000),   // Church 46.15(3)
    ("tptp-pure-fol/SYN/SYN339+1.p", 2000),   // Church 46.15(4)
    ("tptp-pure-fol/SYN/SYN340+1.p", 15000),  // Church 46.15(5) — previously INVALID, hard
    // Other domains
    ("tptp-pure-fol/SYN/SYN036+1.p", 2000),   // Andrews Challenge
    ("tptp-pure-fol/SYN/SYN036+2.p", 2000),   // Andrews Challenge
    ("tptp-pure-fol/PUZ/PUZ031+1.p", 15000),   // Schubert's Steamroller
    ("tptp-pure-fol/PUZ/PUZ060+1.p", 2000),   // Food problem
    ("tptp-pure-fol/PUZ/PUZ061+1.p", 2000),   // Food problem
    ("tptp-pure-fol/MGT/MGT002+1.p", 10000),  // Management (may need warmup)
    ("tptp-pure-fol/MGT/MGT003+1.p", 5000),   // Management
    ("tptp-pure-fol/NLP/NLP001+1.p", 2000),   // NLP
    ("tptp-pure-fol/PUZ/PUZ047+1.p", 5000),   // Wolf/goat/cabbage
    ("tptp-pure-fol/SEU/SEU167+3.p", 5000),   // Set theory theorem 119
  )

  def main(args: Array[String]): Unit = {
    lisa.automation.Tableau.debug = false

    // Find repo root: walk up from user.dir until we find build.sbt
    val startDir = new File(sys.props.getOrElse("user.dir", "."))
    val repoRoot = Iterator.iterate(startDir)(_.getParentFile)
      .takeWhile(_ != null)
      .find(d => new File(d, "build.sbt").exists())
      .getOrElse(startDir)

    var passed = 0
    var failed = 0
    val failures = scala.collection.mutable.ArrayBuffer[String]()

    for ((relPath, maxTime) <- problems) {
      val file = new File(repoRoot, relPath)
      if (!file.exists()) {
        println(s"[SKIP] $relPath — file not found")
      } else {
        val result = TableauBenchmark.runBenchmark(file, maxTime, verify = true)
        val ok = result.solved && result.proofValid.contains(true)
        if (ok) {
          passed += 1
          println(s"[PASS] ${result.solveTimeMs}ms ${result.proofSteps.getOrElse("?")} steps — $relPath")
        } else {
          failed += 1
          val reason = if (!result.solved) result.error.getOrElse("no proof")
                       else if (result.proofValid.contains(false)) "proof INVALID"
                       else "unknown"
          failures += s"$relPath ($reason)"
          println(s"[FAIL] $relPath — $reason")
        }
      }
    }

    println()
    println(s"=== Correctness Baseline: $passed passed, $failed failed out of ${problems.size} ===")
    if (failures.nonEmpty) {
      println("Failures:")
      failures.foreach(f => println(s"  - $f"))
      sys.exit(1)
    }
  }
}
