package lisa.automation.TableauBench

import java.io.File

/**
 * Quick test of specific problems. Prints immediately per-problem results.
 * Usage: runMain lisa.automation.TableauBench.QuickTest [timeoutMs]
 */
object QuickTest {
  // Hand-picked representative problems across domains (self-contained, easy)
  val problems: Seq[String] = Seq(
    // ALG
    "tptp-pure-fol/ALG/ALG211+1.p",
    // COM (2 fail)
    "tptp-pure-fol/COM/COM003+1.p",
    "tptp-pure-fol/COM/COM003+2.p",
    "tptp-pure-fol/COM/COM003+3.p",
    "tptp-pure-fol/COM/COM007+1.p",
    // KRS (some pass, some fail)
    "tptp-pure-fol/KRS/KRS130+1.p",
    "tptp-pure-fol/KRS/KRS132+1.p",
    "tptp-pure-fol/KRS/KRS146+1.p",
    "tptp-pure-fol/KRS/KRS151+1.p",
    "tptp-pure-fol/KRS/KRS153+1.p",
    "tptp-pure-fol/KRS/KRS159+1.p",
    // SET
    "tptp-pure-fol/SET/SET009+3.p",
    "tptp-pure-fol/SET/SET043+1.p",
    "tptp-pure-fol/SET/SET044+1.p",
    "tptp-pure-fol/SET/SET045+1.p",
    "tptp-pure-fol/SET/SET588+3.p",
    "tptp-pure-fol/SET/SET590+3.p",
    "tptp-pure-fol/SET/SET899+1.p",
    // SEU
    "tptp-pure-fol/SEU/SEU158+1.p",
    "tptp-pure-fol/SEU/SEU163+1.p",
    "tptp-pure-fol/SEU/SEU263+1.p",
    "tptp-pure-fol/SEU/SEU264+1.p",
    // SYO
    "tptp-pure-fol/SYO/SYO525+1.015.p",
    "tptp-pure-fol/SYO/SYO578+1.p",
    "tptp-pure-fol/SYO/SYO607+1.p",
    // LCL
    "tptp-pure-fol/LCL/LCL636+1.001.p",
    "tptp-pure-fol/LCL/LCL644+1.001.p",
    "tptp-pure-fol/LCL/LCL644+1.010.p",
    "tptp-pure-fol/LCL/LCL654+1.001.p",
    "tptp-pure-fol/LCL/LCL672+1.001.p",
    // SWB
    "tptp-pure-fol/SWB/SWB001+2.p",
    "tptp-pure-fol/SWB/SWB004+2.p",
    "tptp-pure-fol/SWB/SWB012+2.p",
    "tptp-pure-fol/SWB/SWB016+2.p",
    // MSC
    "tptp-pure-fol/MSC/MSC011+1.p",
    "tptp-pure-fol/MSC/MSC012+1.p",
  )

  def main(args: Array[String]): Unit = {
    val timeoutMs = if args.length > 0 then args(0).toLong else 8000L

    val baseDir = {
      val direct = new File(".")
      if (new File(direct, "tptp-pure-fol").exists()) direct
      else {
        val parent = new File(sys.props.getOrElse("user.dir", ".")).getParentFile
        if (parent != null && new File(parent, "tptp-pure-fol").exists()) parent
        else direct
      }
    }

    var passed = 0
    var failed = 0

    for (relPath <- problems) {
      val pFile = new File(baseDir, relPath)
      if (!pFile.exists()) {
        System.err.println(s"[SKIP] $relPath — not found")
        System.err.flush()
      } else {
        val result = TableauBenchmark.runBenchmark(pFile, timeoutMs, verify = false)
        val status = if result.solved then "PASS" else "FAIL"
        val timeStr = f"${result.solveTimeMs}%5dms"
        val err = if result.solved then "" else s" (${result.error.getOrElse("?")})"
        if (result.solved) passed += 1 else failed += 1
        System.err.println(s"[$status] $timeStr $relPath$err")
        System.err.flush()
      }
    }

    System.err.println(s"\n=== $passed/${passed + failed} passed ===")
    System.err.flush()
  }
}
