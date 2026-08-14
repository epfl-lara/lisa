package lisa.automation.superposition
package bench

import java.io.File
import scala.util.{Try, Success, Failure, Using}

import lisa.utils.K
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import BenchUtil.withTimeout

/**
 * Performance-evaluation harness for the superposition prover (NOT a test -- it has a `main`).
 *
 * [[benchmark]] takes a seeded **random sample** of `n` problems from the generated list of clausal,
 * first-order, equality-free, **unsatisfiable** TPTP problems (`tptp-clausal-fo-noeq-uns.txt`) and tries to
 * solve each within a wall-clock budget. Reproducible: the same seed picks the same sample. Since every
 * problem is unsatisfiable, `REFUTED` vs `TIMEOUT` is the throughput axis, and a `SATURATED` (claiming
 * satisfiable) would itself be a bug.
 *
 * Needs the `TPTP` env var pointing at the TPTP root (the directory containing `Problems/`). Run:
 * {{{
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.bench.Evaluation [seed] [n] [timeoutMs] [maxGiven] [subs] [gen] [unit] [sr] [cond] [equality]"
 * }}}
 * `subs`, `unit`, and `sr` each select a `both` / `fwd` / `bwd` / `none` configuration, for subsumption,
 * unit deletion, and general (multi-literal-side) subsumption resolution respectively; `cond` is `on`/`off`
 * for condensation. Defaults track the engine's: `subs`, `unit` and `sr` on, `cond` off, so a run with no
 * flags measures the configuration that actually ships. `gen` (orthogonal) controls *where*
 * forward simplification runs: `gen` on freshly generated clauses **and** at given-selection; `nogen`
 * (default) only at given-selection. `equality` is `on`/`off` (default on): `off` skips all equality
 * inferences (superposition, equality resolution/factoring, demodulation). This list is equality-free, so
 * `off` measures the cost of the equality machinery running inertly.
 * The solve loop honours `timeoutMs` cooperatively (checked per given clause), so a budgeted run stops
 * cleanly; a daemon-thread hard cap a few seconds later only backstops a pathological single step.
 */
object Evaluation:

  /** The generated full list (paths relative to the TPTP root, e.g. `Problems/SYN/SYN048-1.p`), and the
    * seeded draw from it, shared with the other harnesses so a given seed names the same problems. */
  private val listFileName = "tptp-clausal-fo-noeq-uns.txt"
  private val problems: ProblemList = new ProblemList(listFileName, Some("TPTP_CNF_LIST"))

  def main(args: Array[String]): Unit =
    // The child half of the forked path: solve one problem, print one `RESULT` line, exit. Spawned by
    // [[solveForked]], never invoked by hand.
    if args.headOption.contains("solve1") then { solveChild(args.drop(1)); return }
    val (fwd, bwd) = directionMode(args.lift(4), "subsumption")
    val (fwdUD, bwdUD) = directionMode(args.lift(6), "unit-deletion")
    val (fwdSR, bwdSR) = directionMode(args.lift(7), "subsumption-resolution") // absent ⇒ both, the engine default
    benchmark(
      seed = args.lift(0).map(_.toLong).getOrElse(0L),
      n = args.lift(1).map(_.toInt).getOrElse(100),
      timeoutMs = args.lift(2).map(_.toLong).getOrElse(15000L),
      maxGiven = args.lift(3).map(_.toInt).getOrElse(100000),
      opts = SearchOptions(
        forwardSubsumption = fwd,
        backwardSubsumption = bwd,
        forwardUnitDeletion = fwdUD,
        backwardUnitDeletion = bwdUD,
        forwardSubsumptionResolution = fwdSR,
        backwardSubsumptionResolution = bwdSR,
        condensation = onOffMode(args.lift(8), "condensation", default = false),
        forwardSimplifyAtGeneration = generationMode(args.lift(5)),
        equality = onOffMode(args.lift(9), "equality", default = true))
    )

  /** Parse an `on`/`off` token, falling back to `default` when the argument is absent. */
  private def onOffMode(arg: Option[String], what: String, default: Boolean): Boolean =
    arg.map(_.toLowerCase) match
      case None        => default
      case Some("on")  => true
      case Some("off") => false
      case Some(other) => sys.error(s"unknown $what mode '$other' (use on|off)")

  /** Parse a `both|fwd|bwd|none` direction token into (forward, backward) flags. Default (absent): both on. */
  private def directionMode(arg: Option[String], what: String): (Boolean, Boolean) =
    arg.map(_.toLowerCase) match
      case None | Some("both")            => (true, true)
      case Some("fwd") | Some("forward")  => (true, false)
      case Some("bwd") | Some("backward") => (false, true)
      case Some("none") | Some("off")     => (false, false)
      case Some(other)                    => sys.error(s"unknown $what mode '$other' (use both|fwd|bwd|none)")

  /** Parse the optional forward-simplify-at-generation token (orthogonal to the modes). Default: off
   *  (matches the `Discount` default). `gen` runs forward simplification (subsumption + unit deletion) on
   *  freshly generated clauses **and** at given-selection; `nogen` (default) runs it only at selection. */
  private def generationMode(arg: Option[String]): Boolean =
    arg.map(_.toLowerCase) match
      case None | Some("nogen") => false
      case Some("gen")          => true
      case Some(other)          => sys.error(s"unknown generation mode '$other' (use gen|nogen)")

  /**
   * Randomly pick `n` problems (deterministically from `seed`) out of the generated clausal/no-equality/
   * unsatisfiable list and try to solve each within `timeoutMs` (and `maxGiven`). **Every refutation is reconstructed
   * and run through the kernel checker** (reusing the solve, with no re-proving), so a `bad_proof` in the
   * summary flags a soundness/reconstruction bug. Prints a per-problem row and a summary. A larger `n`
   * than the list size just runs the whole list.
   */
  def benchmark(
      seed: Long,
      n: Int = 100,
      timeoutMs: Long = 15000L,
      maxGiven: Int = 100000,
      opts: SearchOptions = SearchOptions()): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    if !problems.exists then
      println(s"Could not read $listFileName (neither the packaged resource nor $$TPTP_CNF_LIST).")
      return
    val picked: Vector[String] = problems.sample(n, seed)
    val cfg: String =
      s"fwdSubs=${opts.forwardSubsumption} bwdSubs=${opts.backwardSubsumption} fwdUD=${opts.forwardUnitDeletion} bwdUD=${opts.backwardUnitDeletion} " +
        s"fwdSR=${opts.forwardSubsumptionResolution} bwdSR=${opts.backwardSubsumptionResolution} cond=${opts.condensation} " +
        s"fwdSimplifyAtGen=${opts.forwardSimplifyAtGeneration} equality=${opts.equality}"
    val isolation =
      if BenchUtil.forkEnabled then "isolation=fork (one JVM per problem; set LISA_FORK=0 for in-process)"
      else "isolation=thread (LISA_FORK=0; a runaway problem can poison later ones)"
    println(s"list=${problems.describe} (${problems.all.size} problems), seed=$seed, n=${picked.size}, timeout=${timeoutMs}ms, maxGiven=$maxGiven, $cfg, $isolation")
    printHeader()
    report(picked.map(rel => solveRow(new File(tptpRoot.get, rel), timeoutMs, maxGiven, opts)), picked.size)

  private def printHeader(): Unit =
    BenchUtil.resetAbandoned() // this run's contamination count starts here
    println(f"${"PROBLEM"}%-20s ${"SPC"}%-22s ${"CLS"}%4s  ${"RESULT"}%-12s ${"ms"}%8s")

  /** Solve one problem file, kernel-check any refutation, print its table row, and return its result category
   *  and (solve-only) elapsed ms. The solve runs in its own JVM when [[BenchUtil.forkEnabled]]; see the note
   *  on `BenchUtil.runForked` for why. The `SPC`/`CLS` columns are read from the file header here rather than
   *  in the child: they cost no solving and keep the child's job to exactly one thing. */
  private def solveRow(
      f: File,
      timeoutMs: Long,
      maxGiven: Int,
      opts: SearchOptions = SearchOptions()): (String, Long) =
    val name = f.getName
    if !f.exists then
      println(f"$name%-20s ${"-- file not found --"}")
      ("MISSING", 0L)
    else
      val spc = header(f, "SPC").getOrElse("?")
      val cls = clauseCount(f)
      val (result, ms, detail) =
        if BenchUtil.forkEnabled then solveForked(f, timeoutMs, maxGiven, opts)
        else solveOnce(f, timeoutMs, maxGiven, opts, outerTimeout = true)
      println(f"$name%-20s $spc%-22s $cls%4d  $result%-12s $ms%8d$detail")
      (result, ms)

  /** Solve in a fresh JVM and read back the one `RESULT` line. A child that printed none was killed on
    * timeout or died on a fatal error, and those two are now distinguishable, which the in-process path
    * could not manage. */
  private def solveForked(f: File, timeoutMs: Long, maxGiven: Int, opts: SearchOptions): (String, Long, String) =
    val argv = Seq("solve1", f.getPath, timeoutMs.toString, maxGiven.toString, encodeOpts(opts))
    val outcome = BenchUtil.runForked("lisa.automation.superposition.bench.Evaluation", argv, timeoutMs + 5000L)
    outcome.resultLine.flatMap(decodeResult) match
      case Some(r) => r
      case None    =>
        val d = outcome.crashDetail
        (if outcome.timedOut then "HARD_TIMEOUT" else "ERROR", 0L, if d.isEmpty then "" else s"  ($d)")

  /** Child entry: solve one problem, print one machine-readable line, exit. No thread guard: the parent's
    * `destroyForcibly` is the hard cap, and the loop still honours `timeoutMs` cooperatively. */
  private def solveChild(a: Array[String]): Unit =
    val (result, ms, detail) = solveOnce(new File(a(0)), a(1).toLong, a(2).toInt, decodeOpts(a(3)), outerTimeout = false)
    // Tabs separate the fields, so strip any the detail text might contain.
    println(s"${BenchUtil.ResultPrefix}$result\t$ms\t${detail.replace('\t', ' ')}")

  private def decodeResult(line: String): Option[(String, Long, String)] =
    val p = line.stripPrefix(BenchUtil.ResultPrefix).split('\t')
    if p.length < 2 then None else Try((p(0), p(1).toLong, p.lift(2).getOrElse(""))).toOption

  /** The nine knobs the CLI exposes, as a bit string; every other [[SearchOptions]] field keeps its default,
    * exactly as when the parent builds them. Positional and compact, so it stays readable in a process list. */
  private def encodeOpts(o: SearchOptions): String =
    Seq(o.forwardSubsumption, o.backwardSubsumption, o.forwardUnitDeletion, o.backwardUnitDeletion,
      o.forwardSubsumptionResolution, o.backwardSubsumptionResolution, o.condensation,
      o.forwardSimplifyAtGeneration, o.equality).map(if _ then "1" else "0").mkString

  private def decodeOpts(s: String): SearchOptions =
    def b(i: Int): Boolean = s(i) == '1'
    SearchOptions(forwardSubsumption = b(0), backwardSubsumption = b(1), forwardUnitDeletion = b(2),
      backwardUnitDeletion = b(3), forwardSubsumptionResolution = b(4), backwardSubsumptionResolution = b(5),
      condensation = b(6), forwardSimplifyAtGeneration = b(7), equality = b(8))

  /** Parse + solve + check in this JVM. `outerTimeout` adds the thread-based wall-clock guard, wanted when
   *  this *is* the run (`LISA_FORK=0`), redundant in a child whose parent will kill it. */
  private def solveOnce(f: File, timeoutMs: Long, maxGiven: Int, opts: SearchOptions, outerTimeout: Boolean): (String, Long, String) =
    Try(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))) match
      case Failure(e) => ("PARSE_ERR", 0L, s"  ($e)")
      case Success(problem) =>
        val t0 = System.nanoTime()
        // cooperative time budget inside the loop; the hard cap (a killed process, or a daemon thread when
        // in-process) backstops a pathological single step that overshoots between time checks.
        val outcome =
          if outerTimeout then withTimeout(timeoutMs + 5000L)(Bridge.solveTPTPProblem(problem, maxGiven, timeoutMs, opts))
          else Some(Try(Bridge.solveTPTPProblem(problem, maxGiven, timeoutMs, opts)))
        val ms = (System.nanoTime() - t0) / 1000000
        val (result, detail) = outcome match
          case None                                      => ("HARD_TIMEOUT", "")
          case Some(Failure(e))                          => ("ERROR", s"  ($e)")
          case Some(Success(Bridge.Outcome.Saturated))   => ("SATURATED", "")
          case Some(Success(Bridge.Outcome.Timeout))     => ("TIMEOUT", "")
          case Some(Success(s: Bridge.Outcome.Success))  => checkRefutation(s)
        (result, ms, detail)

  /**
   * Reconstruct a refutation's kernel proof and check it. `REFUTED` iff the proof is kernel-valid and
   * concludes the empty sequent `⊢`; otherwise `BAD_PROOF` (a soundness or reconstruction bug). Both halves
   * of the check earn their keep: a reconstruction can produce a kernel-valid proof of the *wrong* sequent, so
   * validity alone would pass it. Reconstruction reuses the solve's bank/inputs (no re-proving).
   * Returns `(category, detail)`.
   */
  private def checkRefutation(s: Bridge.Outcome.Success): (String, String) =
    Try { val p = s.reconstructKernelProof; (p, K.SCProofChecker.checkSCProof(p)) } match
      case Success((p, r)) if r.isValid && p.conclusion == K.Sequent(Set.empty, Set.empty) => ("REFUTED", "")
      case Success((p, r)) => ("BAD_PROOF", s"  (kernelValid=${r.isValid}, conclusion=${p.conclusion})")
      case Failure(e)      => ("BAD_PROOF", s"  (reconstruction threw: $e)")

  /** Aggregate the per-problem categories into the summary line(s). */
  private def report(rows: Seq[(String, Long)], total: Int): Unit =
    def count(c: String): Int = rows.count(_._1 == c)
    val refuted = count("REFUTED")
    val refutedMs = rows.collect { case ("REFUTED", ms) => ms }.sum
    // `saturated` = decided satisfiable; `timeout` = budget hit (status unknown). See Bridge.Outcome.
    // `bad_proof` should always be 0: every refutation is reconstructed and kernel-checked (checkRefutation).
    println(
      s"\nrefuted=$refuted  saturated=${count("SATURATED")}  timeout=${count("TIMEOUT")}  bad_proof=${count("BAD_PROOF")}  " +
        s"hard_timeout=${count("HARD_TIMEOUT")}  error=${count("ERROR")}  parse_err=${count("PARSE_ERR")}  of $total"
    )
    val warning = BenchUtil.contaminationWarning
    if warning.nonEmpty then println(warning)
    if refuted > 0 then println(s"refute time: total=${refutedMs}ms  avg=${refutedMs / refuted}ms")


  /** First TPTP header value for `key` (e.g. `"SPC"`), read from the leading `% key : value` comments. */
  private def header(f: File, key: String): Option[String] =
    Using(scala.io.Source.fromFile(f))(
      _.getLines().find(_.matches(s"%\\s*$key\\s*:.*")).map(_.replaceFirst(s"%\\s*$key\\s*:\\s*", "").trim)
    ).toOption.flatten

  /** Number of `cnf(...)` clauses declared directly in the file (excludes `include`d axioms). */
  private def clauseCount(f: File): Int =
    Using(scala.io.Source.fromFile(f))(_.getLines().count(_.trim.startsWith("cnf("))).getOrElse(0)
