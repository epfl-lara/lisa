package lisa.automation.TableauBench

object ExploreBench {
  def main(args: Array[String]): Unit = {
    val problems = Seq(
      // Rating 0.05 - diverse domains
      "tptp-pure-fol/CSR/CSR025+2.p",
      "tptp-pure-fol/CSR/CSR026+1.p",
      "tptp-pure-fol/GEO/GEO174+1.p",
      "tptp-pure-fol/GEO/GEO191+1.p",
      "tptp-pure-fol/MED/MED001+1.p",
      "tptp-pure-fol/MGT/MGT004+1.p",
      "tptp-pure-fol/MGT/MGT006+1.p",
      "tptp-pure-fol/NUN/NUN088+1.p",
      "tptp-pure-fol/SEV/SEV515+1.p",
      "tptp-pure-fol/SWV/SWV438+1.p",
      "tptp-pure-fol/SYN/SYN036+1.p",
      "tptp-pure-fol/SYN/SYN066+1.p",
      "tptp-pure-fol/SYN/SYN413+1.p",
      "tptp-pure-fol/SYN/SYN941+1.p",
      "tptp-pure-fol/SYN/SYN947+1.p",
      // Rating 0.06 - puzzles/misc
      "tptp-pure-fol/PUZ/PUZ039-1.p",
      "tptp-pure-fol/PUZ/PUZ040-1.p",
      "tptp-pure-fol/MSC/MSC005-1.p",
      // Rating 0.10
      "tptp-pure-fol/COM/COM003+1.p",
      "tptp-pure-fol/MSC/MSC012+1.p",
      // Rating 0.12-0.15
      "tptp-pure-fol/SWB/SWB012+2.p",
      "tptp-pure-fol/KRS/KRS151+1.p",
      "tptp-pure-fol/SET/SET009+3.p",
    )

    val timeout = 8000L
    var passed = 0
    var failed = 0

    // Resolve base dir like QuickTest
    val direct = new java.io.File(".")
    val baseDir = {
      if (new java.io.File(direct, "tptp-pure-fol").exists()) direct
      else {
        val parent = new java.io.File(sys.props.getOrElse("user.dir", ".")).getParentFile
        if (parent != null && new java.io.File(parent, "tptp-pure-fol").exists()) parent
        else direct
      }
    }

    for (p <- problems) {
      val pFile = new java.io.File(baseDir, p)
      if (!pFile.exists()) {
        System.err.println(s"[SKIP] $p — not found")
      } else {
        val result = TableauBenchmark.runBenchmark(pFile, timeoutMs = timeout, verify = false)
        val status = if (result.solved) { passed += 1; "PASS" } else { failed += 1; "FAIL" }
        val msg = f"[$status] ${result.solveTimeMs}%5dms $p${if !result.solved then s" (${result.error.getOrElse("?")})" else ""}"
        System.err.println(msg)
      }
    }

    System.err.println(s"\n=== $passed/${passed + failed} passed ===")
  }
}
