package lisa.automation.clausification

import lisa.automation.clausification.Clausification.Problem
import lisa.automation.clausification.ClausificationStressTest.{problemSize, proofSize, refuteClausalProblem}
import lisa.tptp.{AnnotatedFormula, AnnotatedSequent}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.utils.K.{_, given}

import java.io.File

/** Benchmark the certified clausification pipeline on a random sample of
  * TPTP first-order problems (FOF + CNF, equality allowed).
  *
  * Walks `TPTP-v9.2.1/Problems/<DOMAIN>/<NAME>.p`, keeps files whose TPTP
  * filename suffix marks them as FOF (`+`) or CNF (`-`), draws a deterministic
  * random sample (default 100, default seed 42), parses each via the existing
  * Lisa TPTP parser, builds a `Clausification.Problem` with one hypothesis per
  * axiom (and the conjecture if any), runs `Clausification.certifyClausal`
  * against the [[ClausificationStressTest.refuteClausalProblem]] Sorry-stub
  * back-end (so the wall-clock measures the clausification phase only) under a
  * per-problem timeout, and reports per-problem and aggregate (time, proof
  * size) statistics.
  *
  * Usage:
  *   sbt "lisa-sets/runMain lisa.automation.clausification.ClausificationTPTPBench"
  *   sbt "lisa-sets/runMain lisa.automation.clausification.ClausificationTPTPBench --max 100 --seed 42 --timeout 30000"
  *
  * CLI flags:
  *   --max k          maximum number of problems to run (default 100)
  *   --seed s         RNG seed for sampling (default 42)
  *   --timeout ms     per-problem wall-clock timeout in ms (default 30000)
  *   --max-size n     skip problems whose summed kernel formula size exceeds n
  *                    (default 50000; protects from runaway memory / time)
  *   --tptp path      override the TPTP root (default: TPTP-v9.2.1 in cwd or parent)
  *   --casc path      use the CASC-J12 problem set instead of random TPTP
  *                    (path = directory containing the extracted `Problems/` tree
  *                    from https://tptp.org/CASC/J12/Problems.tgz).
  *                    Restricts to the FOF divisions (FNE + FEQ).  The TPTP root is
  *                    still required to resolve `include('Axioms/...')` directives.
  */
object ClausificationTPTPBench {

  // ─────────────────────────────────────────────────────────────────────────
  // CLI
  // ─────────────────────────────────────────────────────────────────────────

  private case class Cli(
      maxN:           Int    = 100,
      seed:           Long   = 42L,
      timeout:        Long   = 30000L,
      maxSize:        Int    = 50000,
      hardTimeoutMul: Int    = 4,
      maxStuck:       Int    = 3,
      out:            String = "clausification-tptp.csv",
      tptp:           Option[String] = None,
      casc:           Option[String] = None,
      dumpProofs:     Option[String] = None
  )

  private def parseCli(args: Array[String]): Cli = {
    def loop(rest: List[String], acc: Cli): Cli = rest match {
      case Nil => acc
      case "--max"               :: v :: t => loop(t, acc.copy(maxN           = v.toInt))
      case "--seed"              :: v :: t => loop(t, acc.copy(seed           = v.toLong))
      case "--timeout"           :: v :: t => loop(t, acc.copy(timeout        = v.toLong))
      case "--max-size"          :: v :: t => loop(t, acc.copy(maxSize        = v.toInt))
      case "--hard-timeout-mult" :: v :: t => loop(t, acc.copy(hardTimeoutMul = v.toInt))
      case "--max-stuck"         :: v :: t => loop(t, acc.copy(maxStuck       = v.toInt))
      case "--out"               :: v :: t => loop(t, acc.copy(out            = v))
      case "--tptp"              :: v :: t => loop(t, acc.copy(tptp           = Some(v)))
      case "--casc"              :: v :: t => loop(t, acc.copy(casc           = Some(v)))
      case "--dump-proofs"       :: v :: t => loop(t, acc.copy(dumpProofs     = Some(v)))
      case "--help" :: _ | "-h" :: _ =>
        println(
          """ClausificationTPTPBench — random sample of TPTP FOF/CNF problems
            |  --max k                 max problems to run (default 100)
            |  --seed s                RNG seed (default 42)
            |  --timeout ms            per-problem timeout in ms (default 30000)
            |  --max-size n            skip problems with formula-size > n (default 50000)
            |  --hard-timeout-mult k   after a soft timeout, give the worker up to
            |                          k × timeout to actually die before aborting
            |                          the whole benchmark (default 4)
            |  --tptp path             override TPTP root directory
            |  --casc path             use CASC-J12 problem set (FNE+FEQ); path is
            |                          the directory containing Problems/{FNE,FEQ}/...
            |  --dump-proofs dir        write one <name>.proof file per successful run
            |                          into dir (created if absent); skips in-memory
            |                          proof retention for memory savings
            |""".stripMargin)
        sys.exit(0)
      case other :: _ =>
        sys.error(s"Unknown argument: $other")
    }
    loop(args.toList, Cli())
  }

  // ─────────────────────────────────────────────────────────────────────────
  // TPTP root + problem discovery
  // ─────────────────────────────────────────────────────────────────────────

  /** Resolve TPTP root: explicit override, then cwd/TPTP-v9.2.1, then parent/TPTP-v9.2.1. */
  private def resolveTptpRoot(override_ : Option[String]): File = {
    override_.map(new File(_)).filter(_.exists()).getOrElse {
      val cwd = new File(sys.props.getOrElse("user.dir", "."))
      val candidates = Seq(
        new File(cwd, "TPTP-v9.2.1"),
        Option(cwd.getParentFile).map(p => new File(p, "TPTP-v9.2.1")).orNull
      ).filterNot(_ == null).filter(f => f.exists() && new File(f, "Problems").exists())
      candidates.headOption.getOrElse(
        sys.error("Could not locate TPTP-v9.2.1; pass --tptp <path>"))
    }
  }

  /** TPTP filename: domain-prefix (3 letters) + 3 digits + form-tag + version[.M].p
    *
    * Form tags: `+` = FOF, `-` = CNF, `^` = THF, `=` = TFF, `_` = TPI.
    * We keep `+` and `-` only (FOL with optional equality). */
  private val FolFile = """^[A-Z]{3}\d{3}[+\-]\d+(?:\.\d+)?\.p$""".r

  private def listFolProblems(tptpRoot: File): Seq[File] = {
    val problems = new File(tptpRoot, "Problems")
    Option(problems.listFiles()).getOrElse(Array.empty[File])
      .filter(_.isDirectory)
      .toSeq
      .flatMap { dom =>
        Option(dom.listFiles()).getOrElse(Array.empty[File]).toSeq
          .filter(f => FolFile.pattern.matcher(f.getName).matches)
      }
  }

  /** CASC-J12 problem layout: `<root>/Problems/<DIV>/<DIV>ProblemFiles/<NAME>.p`.
    * Restrict to the FOF divisions (FNE = no equality, FEQ = with equality).
    * Exclude CSR (commonsense) problems due to scala-tptp-parser limitations
    * with very large integer literals. */
  private def listCascFolProblems(cascRoot: File): Seq[File] = {
    val problems = new File(cascRoot, "Problems")
    val divs = Seq("FNE", "FEQ")
    divs.flatMap { d =>
      val sub = new File(new File(problems, d), s"${d}ProblemFiles")
      Option(sub.listFiles()).getOrElse(new Array[File](0)).toSeq
        .filter(f => f.isFile && f.getName.endsWith(".p") && !f.getName.startsWith("CSR"))
    }
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Per-problem benchmark
  // ─────────────────────────────────────────────────────────────────────────

  case class Result(
      name:        String,
      domain:      String,
      tag:         String,             // FOF or CNF
      status:      String,             // OK | Skipped | ParseFail | Timeout | Error
      numHyps:     Int,
      hasConj:     Boolean,
      formulaSize: Int,
      proofSize:   Int,
      timeMs:      Double,
      peakMemMb:   Double,              // peak (used heap - baseline) observed during run, in MB
      error:       Option[String]
  )

  /** Pull hypotheses + conjecture from a parsed TPTP `Problem`. */
  private def toClausificationProblem(p: lisa.tptp.Problem): Problem = {
    val hyps = p.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) =>
        (() |- f.formula): Sequent
      case s: AnnotatedSequent if axiomLikeRoles.contains(s.role) =>
        s.sequent
    }
    val conj = p.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => (() |- f.formula): Sequent
      case s: AnnotatedSequent if s.role == "conjecture" => s.sequent
    }
    Problem(hyps, conj)
  }

  /** Tag from filename's form character. */
  private def formTag(name: String): String =
    if (name.contains("+")) "FOF" else if (name.contains("-")) "CNF" else "?"

  /** Threading notes.
    *
    * `Clausification` cooperatively polls `Thread.interrupted()` (and aborts on
    * heap pressure) at most loop boundaries, but a few allocation hotspots can
    * still escape interruption for tens of seconds.  We therefore:
    *
    *  - Run each problem in a daemon worker (so JVM exit is never blocked).
    *  - On soft timeout, send `interrupt()` and wait up to
    *    `--hard-timeout-mult × timeout` for the worker to actually die,
    *    re-interrupting periodically.
    *  - If the worker still won't die, mark the problem as **Stuck** and move
    *    on, leaving the daemon to die in the background.  The next problem
    *    will fail fast via the heap-pressure check in
    *    [[Clausification.checkInterrupted]] if the leaked worker is still
    *    using too much memory.
    *  - Abort the whole benchmark only if too many leaked workers accumulate
    *    (`--max-stuck`), to avoid heap exhaustion.
    *
    * A single benchmarked worker is foreground at any time; only previously
    * stuck workers may be alive in the background. */
  private def runWithTimeout[A](
      timeoutMs:  Long,
      hardCapMs:  Long
  )(thunk: => A): Either[String, (A, Double, Double)] = {
    val resHolder = new java.util.concurrent.atomic.AtomicReference[Either[String, A]](null)
    val done      = new java.util.concurrent.CountDownLatch(1)
    val t0        = System.nanoTime()

    // Per-thread allocation tracking via ThreadMXBean.getThreadAllocatedBytes.
    // This is monotonically increasing, unaffected by GC and other threads, and
    // gives the total bytes allocated by the worker thread — a precise measure of
    // memory pressure regardless of what other threads or GC are doing.
    val tmx = java.lang.management.ManagementFactory.getThreadMXBean match {
      case s: com.sun.management.ThreadMXBean if s.isThreadAllocatedMemorySupported =>
        s.setThreadAllocatedMemoryEnabled(true); Some(s)
      case _ => None
    }
    // allocBefore is read after the thread starts (so the thread ID is known).
    val allocBefore = new java.util.concurrent.atomic.AtomicLong(-1L)
    val allocAfter  = new java.util.concurrent.atomic.AtomicLong(-1L)

    val runnable: Runnable = () => {
      tmx.foreach(t => allocBefore.set(t.getThreadAllocatedBytes(Thread.currentThread().getId)))
      try resHolder.set(Right(thunk))
      catch {
        case _: InterruptedException     => resHolder.set(Left("Interrupted"))
        case oom: OutOfMemoryError       => resHolder.set(Left(s"OOM: ${oom.getMessage}"))
        case e: Throwable                => resHolder.set(Left(s"${e.getClass.getSimpleName}: ${e.getMessage}"))
      } finally {
        tmx.foreach(t => allocAfter.set(t.getThreadAllocatedBytes(Thread.currentThread().getId)))
        done.countDown()
      }
    }

    val thread = new Thread(null, runnable, "clausify-tptp", 64L * 1024 * 1024)
    thread.setDaemon(true)
    thread.start()

    val finished = done.await(timeoutMs, java.util.concurrent.TimeUnit.MILLISECONDS)
    val elapsed  = (System.nanoTime() - t0) / 1e6
    def allocMb: Double = {
      val a = allocAfter.get(); val b = allocBefore.get()
      if (a < 0 || b < 0) 0.0 else math.max(0L, a - b) / (1024.0 * 1024.0)
    }

    if (finished) {
      resHolder.get() match {
        case Right(v)             => Right((v, elapsed, allocMb))
        case Left("Interrupted")  => Left("Timeout")
        case Left(msg)            => Left(msg)
      }
    } else {
      thread.interrupt()
      val grace0   = System.nanoTime()
      val capNanos = hardCapMs * 1000000L
      var lastLogS = 0L
      var stuck    = false
      while (!stuck && !done.await(2000, java.util.concurrent.TimeUnit.MILLISECONDS)) {
        val waitedMs = (System.nanoTime() - grace0) / 1000000L
        val waitedS  = waitedMs / 1000
        if (waitedS - lastLogS >= 5) {
          print(s" [waiting for worker to die: ${waitedS}s]")
          Console.flush()
          lastLogS = waitedS
        }
        thread.interrupt()
        if ((System.nanoTime() - grace0) > capNanos) stuck = true
      }
      if (stuck) {
        // Give up on this problem; leave the daemon to die later. Track count
        // so the main loop can abort if too many accumulate.
        Left("Stuck")
      } else {
        System.gc()
        Left("Timeout")
      }
    }
  }

  private def benchmark(file: File, cli: Cli): Result = {
    val name   = file.getName.stripSuffix(".p")
    // For CASC files the parent dir is `<DIV>ProblemFiles`; fall back to the
    // 3-letter TPTP problem-name prefix in that case.
    val parentName = file.getParentFile.getName
    val domain = if (parentName.endsWith("ProblemFiles")) name.take(3) else parentName
    val tag    = formTag(file.getName)

    val parsed: Either[String, lisa.tptp.Problem] =
      try Right(problemToKernel(file)(using strictMapAtom, strictMapTerm, strictMapVariable))
      catch { case e: Throwable => Left(s"${e.getClass.getSimpleName}: ${e.getMessage}") }

    parsed match {
      case Left(msg) =>
        Result(name, domain, tag, "ParseFail", 0, hasConj = false, 0, 0, 0.0, 0.0, Some(msg))
      case Right(prob) =>
        val cprob   = toClausificationProblem(prob)
        val numHyps = cprob.hypotheses.size
        val hasConj = cprob.conjecture.isDefined
        val fsize   = problemSize(cprob)
        if (fsize > cli.maxSize)
          Result(name, domain, tag, "Skipped", numHyps, hasConj, fsize, 0, 0.0, 0.0,
            Some(s"formula size $fsize > --max-size ${cli.maxSize}"))
        else runWithTimeout(cli.timeout, cli.timeout * cli.hardTimeoutMul.toLong) {
          cli.dumpProofs match {
            case None =>
              proofSize(Clausification.certifyClausal(cprob, refuteClausalProblem))
            case Some(dir) =>
              val outFile = new java.io.File(dir, s"$name.proof")
              val pw = new java.io.PrintWriter(new java.io.BufferedWriter(new java.io.FileWriter(outFile)))
              try {
                val n = Clausification.certifyClausalFlat(cprob, refuteClausalProblem, pw)
                pw.println(s"# end  steps: $n")
                n
              } catch {
                case t: Throwable => try pw.println("# aborted") finally pw.close(); throw t
              } finally pw.close()
          }
        } match {
          case Right((pSize, ms, mem)) =>
            Result(name, domain, tag, "OK", numHyps, hasConj, fsize, pSize, ms, mem, None)
          case Left("Timeout") =>
            Result(name, domain, tag, "Timeout", numHyps, hasConj, fsize, 0, cli.timeout.toDouble, 0.0, None)
          case Left("Stuck") =>
            Result(name, domain, tag, "Stuck", numHyps, hasConj, fsize, 0, cli.timeout.toDouble, 0.0, None)
          case Left(err) =>
            Result(name, domain, tag, "Error", numHyps, hasConj, fsize, 0, 0.0, 0.0, Some(err))
        }
    }
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Reporting
  // ─────────────────────────────────────────────────────────────────────────

  private def percentile(xs: Seq[Double], p: Double): Double = {
    if (xs.isEmpty) 0.0
    else {
      val s = xs.sorted
      val idx = math.min(s.size - 1, math.max(0, math.ceil(p * s.size).toInt - 1))
      s(idx)
    }
  }

  private def report(results: Seq[Result], cli: Cli): Unit = {
    println("\n══════════════════════════════════════════════════════════════")
    println("                      Per-problem results")
    println("══════════════════════════════════════════════════════════════")
    println(f"${"problem"}%-18s ${"dom"}%-4s ${"tag"}%-4s ${"hyps"}%5s ${"conj"}%5s ${"|F|"}%8s ${"|proof|"}%10s ${"time(ms)"}%10s ${"mem(MB)"}%9s  status")
    results.foreach { r =>
      val conjMark = if (r.hasConj) "y" else "-"
      val ps = if (r.proofSize == 0) "-" else r.proofSize.toString
      val tm = if (r.timeMs == 0.0)  "-" else f"${r.timeMs}%.1f"
      val mm = if (r.peakMemMb == 0.0) "-" else f"${r.peakMemMb}%.1f"
      println(f"${r.name}%-18s ${r.domain}%-4s ${r.tag}%-4s ${r.numHyps}%5d ${conjMark}%5s ${r.formulaSize}%8d $ps%10s $tm%10s $mm%9s  ${r.status}")
      r.error.foreach(e => println(s"    ! $e"))
    }

    val byStatus: Map[String, Int] = {
      val m = scala.collection.mutable.HashMap.empty[String, Int].withDefaultValue(0)
      results.foreach(r => m(r.status) = m(r.status) + 1)
      m.toMap.withDefaultValue(0)
    }
    val ok       = results.filter(_.status == "OK")
    val times    = ok.map(_.timeMs)
    val sizes    = ok.map(_.proofSize.toDouble)
    val fsizes   = ok.map(_.formulaSize.toDouble)
    val mems     = ok.map(_.peakMemMb)

    println("\n══════════════════════════════════════════════════════════════")
    println("                          Summary")
    println("══════════════════════════════════════════════════════════════")
    println(f"sample size               : ${results.size}%d")
    println(f"OK                        : ${byStatus("OK")}%d")
    println(f"Timeout (> ${cli.timeout}%d ms)        : ${byStatus("Timeout")}%d")
    println(f"Stuck (worker leaked)     : ${byStatus("Stuck")}%d")
    println(f"Skipped (|F| > ${cli.maxSize}%d) : ${byStatus("Skipped")}%d")
    println(f"ParseFail                 : ${byStatus("ParseFail")}%d")
    println(f"Error                     : ${byStatus("Error")}%d")

    if (ok.nonEmpty) {
      println("\nSuccessful runs (OK only):")
      println(f"  formula size  min/median/p90/max : ${fsizes.min.toLong}%d / ${percentile(fsizes, 0.5).toLong}%d / ${percentile(fsizes, 0.9).toLong}%d / ${fsizes.max.toLong}%d")
      println(f"  proof size    min/median/p90/max : ${sizes.min.toLong}%d / ${percentile(sizes, 0.5).toLong}%d / ${percentile(sizes, 0.9).toLong}%d / ${sizes.max.toLong}%d")
      println(f"  time (ms)     min/median/p90/max : ${times.min}%.1f / ${percentile(times, 0.5)}%.1f / ${percentile(times, 0.9)}%.1f / ${times.max}%.1f")
      println(f"  alloc (MB)    min/median/p90/max : ${mems.min}%.1f / ${percentile(mems, 0.5)}%.1f / ${percentile(mems, 0.9)}%.1f / ${mems.max}%.1f")
      println(f"  total time spent on OK runs      : ${times.sum / 1000.0}%.2f s")
    }
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Main
  // ─────────────────────────────────────────────────────────────────────────

  def main(args: Array[String]): Unit = {
    val cli      = parseCli(args)
    val tptpRoot = resolveTptpRoot(cli.tptp)
    println(s"TPTP root  : ${tptpRoot.getAbsolutePath}")

    cli.dumpProofs.foreach { dir =>
      val d = new java.io.File(dir)
      if (!d.exists()) d.mkdirs()
      println(s"Proofs dir : ${d.getAbsolutePath}")
    }

    val (all, sourceLabel) = cli.casc match {
      case Some(path) =>
        val cascRoot = new File(path)
        if (!cascRoot.exists())
          sys.error(s"--casc path does not exist: $path")
        println(s"CASC root  : ${cascRoot.getAbsolutePath}")
        (listCascFolProblems(cascRoot), s"CASC-J12 FNE+FEQ at ${cascRoot.getAbsolutePath}")
      case None =>
        (listFolProblems(tptpRoot), s"random TPTP at ${tptpRoot.getAbsolutePath}")
    }
    println(s"Source     : $sourceLabel")
    println(s"Discovered : ${all.size} FOF/CNF problem files (TPTP filename suffix `+` or `-`)")

    // Make TPTP env visible to the parser for include directives.
    if (sys.env.get("TPTP").forall(_.isEmpty))
      System.setProperty("TPTP", tptpRoot.getAbsolutePath)
    // Also try to feed it through the JVM's notion of the env: the parser uses sys.env,
    // which is read-only. If TPTP wasn't set externally, problems with includes will fail
    // to parse and be reported as ParseFail — that is the intended behaviour here.

    val rng    = new scala.util.Random(cli.seed)
    val sample = rng.shuffle(all).take(cli.maxN)
    println(s"Sampled    : ${sample.size} problems with seed=${cli.seed}, timeout=${cli.timeout} ms\n")

    val results = scala.collection.mutable.ArrayBuffer.empty[Result]
    var aborted: Option[String] = None
    var stuckCount = 0

    val csv = new java.io.PrintWriter(new java.io.BufferedWriter(new java.io.FileWriter(cli.out)))
    csv.println("problem,domain,tag,status,numHyps,hasConj,formulaSize,proofSize,timeMs,peakMemMb,error")
    csv.flush()
    def emitCsv(r: Result): Unit = {
      def esc(s: String) = "\"" + s.replace("\"", "'") + "\""
      csv.println(s"${r.name},${r.domain},${r.tag},${r.status},${r.numHyps},${r.hasConj},${r.formulaSize},${r.proofSize},${r.timeMs},${r.peakMemMb},${r.error.map(esc).getOrElse("")}")
      csv.flush()
    }

    try {
      val it = sample.zipWithIndex.iterator
      while (it.hasNext && aborted.isEmpty) {
        val (file, i) = it.next()
        print(f"[${i + 1}%3d/${sample.size}%3d] ${file.getParentFile.getName}/${file.getName}%-26s … ")
        Console.flush()
        val r = benchmark(file, cli)
        val tail = r.status match {
          case "OK"      => f"OK     ${r.timeMs}%8.1f ms  |proof|=${r.proofSize}%d  alloc=${r.peakMemMb}%.1f MB"
          case "Skipped" => s"SKIP   (|F|=${r.formulaSize})"
          case s         => s
        }
        println(tail)
        results += r
        emitCsv(r)
        if (r.status == "Stuck") {
          stuckCount += 1
          if (stuckCount > cli.maxStuck)
            aborted = Some(s"$stuckCount stuck workers exceed --max-stuck=${cli.maxStuck}")
        }
      }
    } catch {
      case e: RuntimeException =>
        aborted = Some(e.getMessage)
      case e: OutOfMemoryError =>
        aborted = Some(s"OOM in main: ${e.getMessage}")
    } finally {
      try csv.close() catch { case _: Throwable => () }
    }
    aborted.foreach(msg => println(s"\n!! Benchmark aborted: $msg"))
    println(s"CSV written to: ${cli.out}")

    try report(results.toSeq, cli)
    catch {
      case e: OutOfMemoryError =>
        println(s"\n!! Out of memory while computing report: ${e.getMessage}")
        println(s"   Per-problem CSV is at: ${cli.out}")
    }
    aborted.foreach(_ => sys.exit(2))
  }
}
