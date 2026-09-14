package lisa.automation.superposition
package bench

import lisa.automation.Problem
import lisa.automation.clausification.CertifiedClausifier
import lisa.automation.clausification.Clausification.ClausifierOptions
import lisa.automation.clausification.Clausification.Distribute
import lisa.automation.clausification.Clausification.GeneratedNames
import lisa.automation.clausification.Clausification.Prenex

import lisa.automation.clausification.UncertifiedClausifier
import lisa.tptp.KernelParser.problemToKernel
import lisa.tptp.KernelParser.strictMapAtom
import lisa.tptp.KernelParser.strictMapTerm
import lisa.tptp.KernelParser.strictMapVariable
import lisa.utils.K

import java.io.File
import scala.util.Failure
import scala.util.Success
import scala.util.Try
import scala.util.Using

import BenchUtil.withTimeout
import BenchUtil.median

/**
 * Runs a dataset through the whole pipeline: clausify, refute, kernel-check the composed proof. A `bad_proof`
 * row is therefore a reconstruction or composition bug. The clausifiers take a `Problem => SCProof`, so the
 * prover is called mid-descent and is timed inside its own closure.
 *
 * `mode=uncert` is a separate pipeline: it clausifies without a certificate, searches and prints TSTP, building
 * no kernel proof, so the difference between the two modes is the cost of certification.
 *
 * A dataset object such as [[FofEvaluation]] names only the list it draws from. Requires `TPTP` to point at the
 * problem library.
 *
 * {{{
 *   [key=value]…       run the benchmark; see [[Config]] for the keys
 *   sample [n] [seed]  print the drawn paths, so another prover can run the same set
 *   files <listfile>   run an explicit list of TPTP-relative paths, with no sampling
 *   verify <rel>…      clausify one problem both ways and report the checker's verdict in full
 * }}}
 *
 * @param childMainClass the object whose `main` a forked child re-enters, so that it reads the same list
 */
final class Harness(listFileName: String, listEnvVar: String, childMainClass: String):

  private val problems: ProblemList = new ProblemList(listFileName, Some(listEnvVar))

  /**
   * Every problem path in the list, relative to the TPTP root, in file order.
   */
  def allProblems: Vector[String] = problems.all

  /**
   * A reproducible sample of `n` problems drawn with `seed`; an `n` past the list returns all of it.
   */
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = problems.sample(n, seed)

  // ── configuration ─────────────────────────────────────────────────────────────────────────────────────────

  /**
   * One run's settings. `seed`/`n` choose the sample, `timeoutMs` and `opts.maxGiven` bound each problem,
   * `maxSize` skips problems whose summed formula size would blow up clausification, and `certified` picks
   * the clausifier. `raw` is the command line that produced this, handed to a forked child unchanged.
   */
  final case class Config(
      seed: Long = 42,
      n: Int = 100,
      timeoutMs: Long = 15000L,
      maxSize: Int = 50000,
      limit: Int = Int.MaxValue, //  truncate the problem list, for dry runs
      clausifyOnly: Boolean = false, //  clausify and check that derivation, but do not search
      // Run the kernel check, which `timeoutMs` does not bound. Off, `uses_sorry` is false because nothing looked.
      check: Boolean = true,
      clausifier: ClausifierOptions = ClausifierOptions(),
      certified: Boolean = true,
      opts: SearchOptions = SearchOptions(maxGiven = 100000),
      // Where the listed problems live, if not the TPTP library (e.g. the scrambled CASC copies). `$TPTP` is
      // still required to resolve `include`s.
      problemRoot: Option[String] = None,
      // The CSV's `problem` column, when the file name is not the problem's (StarExec's `theBenchmark.p`).
      problemName: String = "",
      dataset: String = "", //   the CSV's `dataset` column, set by the driver
      configName: String = "", //  the CSV's `config` column, naming this point of the matrix
      strategy: String = "", //  the CSV's `strategy` column, empty for a single-strategy run
      csvOut: Option[String] = None,
      // Print the TSTP derivation, as CASC wants. Set only by the single-problem entry point.
      tstpOut: Boolean = false,
      // Count `timeoutMs` from JVM start rather than from the search. Set only where one JVM handles one problem.
      wallBudget: Boolean = false,
      raw: Seq[String] = Nil
  ):
    def mode: String = if certified then "certified" else "uncertified"

  /**
   * Parse `key=value` arguments. Recognised keys: `seed`, `n`, `timeout`, `given`, `size`, `mode` (`cert` or
   * `uncert`), and any search flag named by [[withFlag]], each taking `on`/`off`.
   */
  private def parse(args: Seq[String]): Config =
    args.foldLeft(Config(raw = args)) { (c, arg) =>
      val (key, value) = arg.span(_ != '=') match { case (k, v) => (k, v.drop(1)) }
      def flag: Boolean = value.toLowerCase match
        case "on" | "true" | "1" => true
        case "off" | "false" | "0" => false
        case other => sys.error(s"'$key' takes on|off, got '$other'")
      key match
        case "seed" => c.copy(seed = value.toLong)
        case "n" => c.copy(n = value.toInt)
        case "timeout" => c.copy(timeoutMs = value.toLong)
        case "given" => c.copy(opts = c.opts.copy(maxGiven = value.toInt))
        case "size" => c.copy(maxSize = value.toInt)
        case "limit" => c.copy(limit = value.toInt)
        case "clausifyOnly" => c.copy(clausifyOnly = flag)
        case "check" => c.copy(check = flag)
        case "prenex" =>
          c.copy(clausifier = c.clausifier.copy(prenex = value.toLowerCase match
            case "deconstruct" => Prenex.Deconstruct
            case "rewrite" => Prenex.Rewrite
            case other => sys.error(s"prenex takes deconstruct|rewrite, got '$other'")))
        case "threshold" => c.copy(clausifier = c.clausifier.copy(threshold = value.toInt))
        case "distribute" =>
          c.copy(clausifier = c.clausifier.copy(distribute = value.toLowerCase match
            case "weakening" => Distribute.Weakening
            case "primitive" => Distribute.Primitive
            case other => sys.error(s"distribute takes weakening|primitive, got '$other'")))
        case "mode" => c.copy(certified = value.toLowerCase != "uncert")
        // `strategy` replaces the whole option record, so it must come before any flag meant to override it.
        case "strategy" =>
          val s = Strategy.byName(value).getOrElse(sys.error(s"unknown strategy '$value'; have ${Strategy.portfolio.map(_.name).mkString(", ")}"))
          c.copy(strategy = value, opts = s.opts.copy(maxGiven = c.opts.maxGiven, maxMillis = c.opts.maxMillis))
        case "orthologic" => c.copy(opts = c.opts.copy(orthologic = flag))
        case "sine" => c.copy(opts = c.opts.copy(sine = if flag then Some(c.opts.sine.getOrElse(SineConfig())) else None))
        case "sineTol" => c.copy(opts = c.opts.copy(sine = Some(c.opts.sine.getOrElse(SineConfig()).copy(tolerance = value.toDouble))))
        case "sineDepth" => c.copy(opts = c.opts.copy(sine = Some(c.opts.sine.getOrElse(SineConfig()).copy(depth = value.toInt))))
        // The hypothesis count below which SInE keeps everything. Unlike `sineTol` and `sineDepth`, it only
        // adjusts an existing SInE configuration, so an A/B on it does not also switch selection on.
        case "sineMin" => c.copy(opts = c.opts.copy(sine = c.opts.sine.map(_.copy(minAxioms = value.toInt))))
        case "fwdUDIndex" => c.copy(opts = c.opts.copy(forwardUnitDeletionIndexThreshold = value.toInt))
        case "root" => c.copy(problemRoot = Some(value))
        case "problem" => c.copy(problemName = value)
        case "dataset" => c.copy(dataset = value)
        case "config" => c.copy(configName = value)
        case "out" => c.copy(csvOut = Some(value))
        case _ => c.copy(opts = withFlag(c.opts, key, flag))
    }

  /**
   * The search flags the command line can set by name. Everything else keeps its [[SearchOptions]] default.
   */
  private def withFlag(o: SearchOptions, key: String, on: Boolean): SearchOptions = key match
    case "equality" => o.copy(equality = on)
    case "superposition" => o.copy(superposition = on)
    case "fwdSubs" => o.copy(forwardSubsumption = on)
    case "bwdSubs" => o.copy(backwardSubsumption = on)
    case "fwdUD" => o.copy(forwardUnitDeletion = on)
    case "bwdUD" => o.copy(backwardUnitDeletion = on)
    case "fwdSR" => o.copy(forwardSubsumptionResolution = on)
    case "bwdSR" => o.copy(backwardSubsumptionResolution = on)
    case "fwdDemod" => o.copy(forwardDemodulation = on)
    case "bwdDemod" => o.copy(backwardDemodulation = on)
    case "cond" => o.copy(condensation = on)
    case "genSimplify" => o.copy(forwardSimplifyAtGeneration = on)
    case other => sys.error(s"unknown option '$other'")

  // ── CLI ───────────────────────────────────────────────────────────────────────────────────────────────────

  def main(args: Array[String]): Unit = args.toSeq match
    // The child half of the forked path: solve exactly one problem, print one `RESULT` line, exit. It re-parses
    // the parent's own arguments, so the two runs are configured by the same code.
    case "solve1" +: file +: rest => solveChild(file, rest)
    case "sample" +: rest =>
      sample(rest.lift(0).map(_.toInt).getOrElse(100), rest.lift(1).map(_.toLong).getOrElse(42L)).foreach(println)
    case "verify" +: rest => rest.foreach(verifyOne)
    case "one" +: file +: outDir +: rest => runOne(file, outDir, parse(rest))
    case "files" +: list +: rest => runFiles(list, parse(rest))
    case rest => benchmark(parse(rest))

  /**
   * One problem, for a cluster that schedules problems itself (StarExec): writes the CSV row into `outDir` and
   * prints the SZS status line the cluster reads. In-process, since the cluster already isolates each run and a
   * fork would put a second JVM start inside the budget.
   */
  private def runOne(file: String, outDir: String, cfg0: Config): Unit =
    val f = new File(file)
    val out = new File(outDir)
    out.mkdirs()
    val cfg = cfg0.copy(maxSize = Int.MaxValue, csvOut = Some(new File(out, "result.csv").getPath), tstpOut = true, wallBudget = true)
    // StarExec names every benchmark `theBenchmark.p`, so `problem=` carries the real name when given.
    val name = if cfg.problemName.nonEmpty then cfg.problemName else f.getName

    // Write a row even when killed from outside by SIGTERM, so unsolved problems keep their counters. SIGKILL
    // cannot be caught.
    val written = new java.util.concurrent.atomic.AtomicBoolean(false)
    Runtime.getRuntime.addShutdownHook(new Thread(() =>
      if written.compareAndSet(false, true) then
        writeCsv(cfg.csvOut.get, Vector((name, Timing("KILLED", detail = "killed before finishing"))), cfg)
        println(s"% SZS status Timeout for $name")
    ))

    val (hyps, cj, res) = solveLocal(f, cfg, outerTimeout = true)
    val timing = res.copy(hypotheses = hyps) // as `solveRow` does
    val hasConjecture = cj == "y"
    // Anything that is neither a refutation nor a timeout is `GaveUp`, not a claim we cannot support.
    val szs = timing.category match
      case "REFUTED" => if hasConjecture then "Theorem" else "Unsatisfiable"
      // Never `(Counter)Satisfiable`, as in [[CascProver]]: SInE may have dropped axioms the proof needed.
      case "SATURATED" => "GaveUp"
      case "CLAUSIFIED" => "GaveUp" // clausify-only: nothing was proved
      case "TIMEOUT" | "HARD_TIMEOUT" => "Timeout"
      case _ => "GaveUp"
    if written.compareAndSet(false, true) then
      writeCsv(cfg.csvOut.get, Vector((name, timing)), cfg)
      println(s"% SZS status $szs for $name")
      // The derivation follows the status line; only the uncertified path produces one.
      timing.tstp.foreach(print)

  /**
   * Draw a seeded sample and run each problem.
   */
  def benchmark(cfg: Config): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    val picked = sample(cfg.n, cfg.seed)
    println(
      s"list=${problems.describe} (${allProblems.size} problems), seed=${cfg.seed}, n=${picked.size}, " +
        s"timeout=${cfg.timeoutMs}ms, maxGiven=${cfg.opts.maxGiven}, maxSize=${cfg.maxSize}, mode=${cfg.mode}, " +
        s"equality=${cfg.opts.equality}, ${BenchUtil.isolationBanner}"
    )
    run(picked, cfg.problemRoot.map(new File(_)).getOrElse(tptpRoot.get), cfg)

  /**
   * Run an explicit list of TPTP-root-relative paths, one per line, with no sampling and no size guard.
   */
  private def runFiles(listPath: String, cfg0: Config): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    val all = Using(scala.io.Source.fromFile(listPath))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get
    val paths = all.take(cfg0.limit)
    val cfg = cfg0.copy(maxSize = Int.MaxValue)
    val root = cfg.problemRoot.map(new File(_)).getOrElse(tptpRoot.get)
    println(
      s"files=$listPath (${paths.size} of ${all.size} problems), root=$root, timeout=${cfg.timeoutMs}ms, " +
        s"maxGiven=${cfg.opts.maxGiven}, mode=${cfg.mode}, ${BenchUtil.isolationBanner}"
    )
    run(paths, root, cfg)

  /** Run each listed problem, resolved against `root` (the TPTP library unless `root=` said otherwise). */
  private def run(paths: Vector[String], root: File, cfg: Config): Unit =
    println(f" ${"PROBLEM"}%-19s ${"HYP"}%4s ${"CJ"}%3s  ${"RESULT"}%-12s ${"clausify"}%10s ${"search"}%9s ${"recon"}%8s ${"check"}%9s ${"given"}%9s")
    val rows = paths.map(rel => (rel, solveRow(new File(root, rel), cfg)))
    cfg.csvOut.foreach(writeCsv(_, rows, cfg))
    report(rows.map(_._2), paths.size)

  // ── CSV ───────────────────────────────────────────────────────────────────────────────────────────────────

  /**
   * The columns every run writes, whatever it was launched to answer, so that one analysis reads them all.
   */
  private val CsvHeader: Seq[String] = Seq(
    "dataset", "problem", "config", "strategy", "verdict",
    "hypotheses",
    "clausify_ms", "search_ms", "reconstruct_ms", "check_ms",
    "given", "derived", "peak_active", "peak_passive",
    "clauses", "fresh_symbols",
    "proof_steps", "raw_size", "shared_size", "max_sequent", "imports",
    "uses_sorry", "detail"
  )

  /**
   * One row per problem. A quantity this run did not produce is written empty, never zero, so that aggregates
   * do not count it as measured.
   */
  private def writeCsv(path: String, rows: Vector[(String, Timing)], cfg: Config): Unit =
    def opt(i: Int): String = if i < 0 then "" else i.toString
    def ms(reached: Boolean, d: Double): String = if reached then f"$d%.3f" else ""
    def cnt(reached: Boolean, i: Int): String = if reached then i.toString else ""
    val out = new java.io.PrintWriter(new File(path), "UTF-8")
    try
      out.println(CsvHeader.mkString(","))
      rows.foreach { (rel, t) =>
        val reached = ReachedProver(t.category)
        val m = t.metrics
        val cells = Seq(
          cfg.dataset, rel, cfg.configName, cfg.strategy, t.category,
          opt(t.hypotheses),
          f"${t.clausifyMs}%.3f", ms(reached, t.searchMs),
          // Only when a kernel proof was built (`metrics` present); the uncertified path builds none.
          if m.isDefined then f"${t.reconstructMs}%.3f" else "",
          if m.isDefined then f"${t.checkMs}%.3f" else "",
          // Empty rather than the default 0 for a problem that never searched.
          cnt(reached, t.givenProcessed), cnt(reached, t.derived), cnt(reached, t.peakActive), cnt(reached, t.peakPassive),
          opt(t.clauses), opt(t.freshSymbols),
          m.map(_.steps.toString).getOrElse(""), m.map(_.rawSize.toString).getOrElse(""),
          m.map(_.sharedSize.toString).getOrElse(""), m.map(_.maxSequent.toString).getOrElse(""),
          m.map(_.imports.toString).getOrElse(""),
          if m.isDefined then t.usesSorry.toString else "",
          t.detail
        )
        out.println(cells.map(csvCell).mkString(","))
      }
    finally out.close()
    println(s"wrote ${rows.size} rows to $path")

  /** Quote a cell only when it needs it, so the common case stays readable. */
  private def csvCell(s: String): String =
    if s.exists(c => c == ',' || c == '"' || c == '\n') then "\"" + s.replace("\"", "\"\"") + "\"" else s

  // ── one problem ───────────────────────────────────────────────────────────────────────────────────────────

  /**
   * Per-problem outcome and where the wall-clock went: `clausifyMs` (everything outside the prover call),
   * `searchMs` (the saturation), `reconstructMs` (building the kernel proof), `checkMs` (the kernel check),
   * plus the loop-scale counters.
   */
  private final case class Timing(
      category: String,
      clausifyMs: Double = 0.0,
      searchMs: Double = 0.0,
      reconstructMs: Double = 0.0,
      checkMs: Double = 0.0,
      givenProcessed: Int = 0,
      derived: Int = 0,
      peakActive: Int = 0,
      peakPassive: Int = 0,
      hypotheses: Int = -1, //      hypotheses the problem carries; -1 when unknown
      clauses: Int = -1, //         clauses handed to the prover; -1 when it was never reached
      freshSymbols: Int = -1, //    naming atoms and Skolem symbols in those clauses
      metrics: Option[ProofMetrics] = None, //  present when a proof was built
      usesSorry: Boolean = false,
      detail: String = "",
      // The uncertified path's TSTP derivation. Not a CSV column; only the single-problem entry point prints it.
      tstp: Option[String] = None
  )

  /**
   * Categories whose problem reached the prover, i.e. clausified without error.
   */
  private val ReachedProver: Set[String] = Set("REFUTED", "SATURATED", "TIMEOUT", "BAD_PROOF", "EXHAUSTED")

  /**
   * Solve one problem and print its row, in its own JVM when [[BenchUtil.forkEnabled]], else in-process.
   */
  private def solveRow(f: File, cfg: Config): Timing =
    val name = f.getName
    if !f.exists then { println(f" $name%-19s ${"-- file not found --"}"); return Timing("MISSING") }
    val (hyps, cj, res0) =
      if BenchUtil.forkEnabled then solveForked(f, cfg)
      else solveLocal(f, cfg, outerTimeout = true)
    val res = res0.copy(hypotheses = hyps)
    val h = if hyps < 0 then "?" else hyps.toString
    val detail = if res.detail.isEmpty then "" else s"  (${res.detail})"
    println(f" $name%-19s $h%4s $cj%3s  ${res.category}%-12s ${res.clausifyMs}%10.1f ${res.searchMs}%9.1f ${res.reconstructMs}%8.1f ${res.checkMs}%9.1f ${res.givenProcessed}%9d$detail")
    res

  /**
   * Run this problem in a fresh JVM and read back its one `RESULT` line. A child that printed none was killed
   * on timeout or died on a fatal error, and the two are distinguishable.
   */
  private def solveForked(f: File, cfg: Config): (Int, String, Timing) =
    val outcome = BenchUtil.runForked(childMainClass, Seq("solve1", f.getPath) ++ cfg.raw, cfg.timeoutMs + 5000L)
    outcome.resultLine.flatMap(decodeRow).getOrElse((-1, "?", Timing(if outcome.timedOut then "HARD_TIMEOUT" else "PROVER_CRASH", detail = outcome.crashDetail)))

  /**
   * Child entry: solve one problem, print one machine-readable line, exit. No outer timeout, since the
   * parent's `destroyForcibly` is the hard cap and the loop still honours `timeoutMs` cooperatively.
   */
  private def solveChild(file: String, args: Seq[String]): Unit =
    // `publish` prints a row before the unbounded kernel check. The parent reads the last `RESULT` line, so that
    // row survives if the child is killed during the check.
    val (hyps, cj, t) = solveLocal(new File(file), parse(args), outerTimeout = false,
                                   publish = (h, c, p) => println(encodeRow(h, c, p)))
    println(encodeRow(hyps, cj, t))

  // Plain `toString`/`toDouble` rather than the `f` interpolator: `%f` formats in the default locale, writing
  // `0,3` where the parser expects `0.3`.
  private def encodeRow(hyps: Int, cj: String, t: Timing): String =
    Seq(
      t.category,
      hyps.toString,
      cj,
      t.clausifyMs.toString,
      t.searchMs.toString,
      t.reconstructMs.toString,
      t.checkMs.toString,
      t.givenProcessed.toString,
      t.derived.toString,
      t.peakActive.toString,
      t.peakPassive.toString,
      t.clauses.toString,
      t.freshSymbols.toString,
      // `-` for absent, since a child that built no proof has no metrics to send.
      t.metrics.fold("-")(m => s"${m.steps} ${m.rawSize} ${m.sharedSize} ${m.maxSequent} ${m.imports}"),
      t.usesSorry.toString,
      t.detail
    ).mkString(BenchUtil.ResultPrefix, "\t", "")

  private def decodeRow(line: String): Option[(Int, String, Timing)] =
    val p = line.stripPrefix(BenchUtil.ResultPrefix).split('\t')
    if p.length < 15 then None
    else
      Try {
        val metrics = p(13) match
          case "-" => None
          case s =>
            val f = s.split(' ')
            Some(ProofMetrics(f(0).toInt, f(1).toLong, f(2).toLong, f(3).toLong, f(4).toInt))
        // Named arguments, so a field added to `Timing` cannot shift the others. `hypotheses` travels as `p(1)`.
        (p(1).toInt, p(2), Timing(
          category = p(0),
          clausifyMs = p(3).toDouble, searchMs = p(4).toDouble, reconstructMs = p(5).toDouble, checkMs = p(6).toDouble,
          givenProcessed = p(7).toInt, derived = p(8).toInt, peakActive = p(9).toInt, peakPassive = p(10).toInt,
          clauses = p(11).toInt, freshSymbols = p(12).toInt,
          metrics = metrics, usesSorry = p(14).toBoolean, detail = p.lift(15).getOrElse("")
        ))
      }.toOption

  /**
   * Parse, clausify and solve one problem in this JVM. `outerTimeout` adds the thread-based wall-clock guard,
   * wanted when this *is* the run (`LISA_FORK=0`), redundant in a child whose parent will kill it.
   */
  private def solveLocal(f: File, cfg0: Config, outerTimeout: Boolean,
                         publish: (Int, String, Timing) => Unit = (_, _, _) => ()): (Int, String, Timing) =
    if !f.exists then return (-1, "?", Timing("MISSING"))
    // Catch `Throwable`, not just `NonFatal`: the recursive TPTP parser can `StackOverflowError` on very
    // deeply-nested formulas, which would otherwise kill the whole run.
    (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
    catch { case e: Throwable => Failure(e) }) match
      case Failure(e) => (-1, "?", Timing("PARSE_ERR", detail = e.getClass.getSimpleName))
      case Success(parsed) =>
        // With `wallBudget`, JVM uptime (start-up and parsing) comes out of the budget. Not for batch runs,
        // where uptime accumulates across problems.
        val cfg = if cfg0.wallBudget then cfg0.copy(timeoutMs = math.max(5000L, cfg0.timeoutMs - java.lang.management.ManagementFactory.getRuntimeMXBean.getUptime)) else cfg0
        val cprob = Prover.fromTptp(parsed)
        val hyps = cprob.hypotheses.size
        val cj = if cprob.conjecture.isDefined then "y" else "-"
        val size = cprob.size
        if size > cfg.maxSize then (hyps, cj, Timing("SKIPPED", detail = s"|F|=$size > ${cfg.maxSize}"))
        else if !outerTimeout then
          (
            hyps,
            cj,
            try solveOne(cprob, cfg, parsed, f.getName, t => publish(hyps, cj, t))
            catch { case e: Throwable => Timing(s"ERROR(${e.getClass.getSimpleName})") }
          )
        else
          (
            hyps,
            cj,
            withTimeout(cfg.timeoutMs + 5000L)(solveOne(cprob, cfg, parsed, f.getName, t => publish(hyps, cj, t))) match
              case Some(Success(t)) => t
              case Some(Failure(e)) => Timing(s"ERROR(${e.getClass.getSimpleName})")
              case None => Timing("HARD_TIMEOUT")
          )

  /**
   * A non-refutation thrown by the prover to abort the clausification it was called from.
   */
  private final class NonRefutation(val outcome: Clausal.Outcome) extends RuntimeException

  /**
   * A throw from the prover closure, kept distinct from a clausification throw so that it is categorised
   * `BAD_PROOF` rather than `CLAUSIFY_ERR`.
   */
  private final class ProverError(cause: Throwable) extends RuntimeException(cause)

  /**
   * The uncertified pipeline: clausify without a certificate, search, and print the refutation as TSTP, through
   * [[Prover.proveTstp]] as [[CascProver]] does. No kernel proof is built, so `reconstructMs`, `checkMs` and the
   * proof metrics are absent rather than zero.
   */
  private def solveUncertified(cprob: Problem, cfg: Config, parsed: lisa.tptp.TptpProblem, name: String): Timing =
    val stats = new java.util.concurrent.atomic.AtomicReference[Discount.LoopStats](Discount.LoopStats(0, 0, 0, 0))
    // `proveTstp` clausifies and then searches; the callback between them is what splits the two phases.
    val clausifiedAt = new java.util.concurrent.atomic.AtomicLong(0L)
    val t0 = System.nanoTime()
    def split(end: Long): (Double, Double) =
      val mark = clausifiedAt.get
      if mark == 0L then ((end - t0) / 1e6, 0.0) //  never reached the search
      else ((mark - t0) / 1e6, (end - mark) / 1e6)
    val opts = cfg.opts.copy(maxMillis = cfg.timeoutMs, onStats = stats.set)
    val base: Timing =
      try
        val result = Prover.proveTstp(cprob, opts, () => clausifiedAt.set(System.nanoTime()))
        val (clausifyMs, searchMs) = split(System.nanoTime())
        result match
          case Right(r) =>
            // Captured, since the caller prints the SZS status line before it.
            val tstp = Option.when(cfg.tstpOut) {
              val buffer = new java.io.ByteArrayOutputStream()
              val (inputFormulas, conjecture) = Tstp.inputFormulas(parsed, cprob)
              Console.withOut(buffer) {
                Tstp.printRefutation(name, r.axioms.map(inputFormulas), conjecture, r.clauses, r.success,
                                     isCnf = parsed.spc.exists(_.contains("CNF")))
              }
              buffer.toString
            }
            Timing("REFUTED", clausifyMs, searchMs, clauses = r.clauses.size, tstp = tstp)
          case Left(Clausal.Outcome.Saturated) => Timing("SATURATED", clausifyMs, searchMs)
          case Left(Clausal.Outcome.Timeout) => Timing("TIMEOUT", clausifyMs, searchMs)
          case Left(_) => Timing("UNKNOWN", clausifyMs, searchMs)
      catch
        case _: InterruptedException =>
          val (clausifyMs, searchMs) = split(System.nanoTime())
          Timing("TIMEOUT", clausifyMs, searchMs)
        case e: Throwable =>
          val (clausifyMs, searchMs) = split(System.nanoTime())
          val where = e.getStackTrace.headOption.fold("")(t => s" at ${t.getClassName.split('.').last}.${t.getMethodName}:${t.getLineNumber}")
          val what = s"${e.getClass.getSimpleName}: ${Option(e.getMessage).getOrElse("")}$where"
          // Running out of heap or stack is a resource limit, not a defect.
          val cat = if e.isInstanceOf[OutOfMemoryError] || e.isInstanceOf[StackOverflowError] then "EXHAUSTED" else s"ERROR(${e.getClass.getSimpleName})"
          Timing(cat, clausifyMs, searchMs, detail = what.replace(',', ';').replace('\n', ' ').take(300))
    val s = stats.get
    base.copy(givenProcessed = s.givenProcessed, derived = s.passiveEnqueued, peakActive = s.peakActive, peakPassive = s.peakPassive)

  /**
   * Run the pipeline once, timing each phase and recording the loop-scale stats.
   */
  private def solveOne(cprob: Problem, cfg: Config, parsed: lisa.tptp.TptpProblem, name: String,
                       publish: Timing => Unit = _ => ()): Timing =
    // A separate pipeline that builds no kernel proof; see [[solveUncertified]].
    if !cfg.certified && !cfg.clausifyOnly then return solveUncertified(cprob, cfg, parsed, name)
    val searchNanos = new java.util.concurrent.atomic.AtomicLong(0L)
    val reconstructNanos = new java.util.concurrent.atomic.AtomicLong(0L)
    val clauseCount = new java.util.concurrent.atomic.AtomicInteger(-1)
    val freshCount = new java.util.concurrent.atomic.AtomicInteger(-1)
    def proverNanos: Long = searchNanos.get + reconstructNanos.get
    val stats = new java.util.concurrent.atomic.AtomicReference[Discount.LoopStats](Discount.LoopStats(0, 0, 0, 0))
    // `Clausal.prove` inlined, to time search and reconstruction apart. Both accumulate: the clausifier may call
    // this closure more than once. `goal` holds the goal clauses from `certifyClausalGoal`.
    val prover: (Problem, Set[Int]) => K.SCProof = (p, goal) =>
      try
        clauseCount.set(p.imports.size)
        freshCount.set(freshSymbolsOf(p))
        // Clausify-only: close with a `Sorry` and never search, so only the clausification derivation is checked.
        if cfg.clausifyOnly then K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), p.imports)
        else
          val prepared = Clausal.prepare(p)
          val ss = System.nanoTime()
          val outcome =
            try Clausal.refute(prepared.work, cfg.opts.copy(maxMillis = cfg.timeoutMs, onStats = stats.set),
                               symbolVars = prepared.symbolVars, discharge = prepared.abs.dischargeSubst, goal = goal)
            finally searchNanos.addAndGet(System.nanoTime() - ss)
          outcome match
            case s: Clausal.Outcome.Success =>
              val rs = System.nanoTime()
              try Clausal.composeProof(s.reconstructKernelProof, prepared.orig)
              finally reconstructNanos.addAndGet(System.nanoTime() - rs)
            case other => throw new NonRefutation(other)
      catch
        case nr: NonRefutation => throw nr // a decided non-refutation: propagate to the SATURATED/TIMEOUT arm
        case ie: InterruptedException => throw ie // hard-timeout interrupt: propagate to the TIMEOUT arm
        case e: Throwable => throw new ProverError(e)
    val t0 = System.nanoTime()
    def clausifyMsSoFar: Double = (System.nanoTime() - t0 - proverNanos) / 1e6
    val base: Timing =
      try
        // Through `preprocessKernel`, so SInE and orthologic normalisation apply as in `Prover.proveKernel`.
        val proof =
          if cfg.certified then Prover.preprocessKernel(cprob, cfg.opts)(CertifiedClausifier.certifyClausalGoal(_, prover, cfg.clausifier))
          else UncertifiedClausifier.uncertifyClausal(cprob, p => prover(p, Set.empty))
        val clausifyMs = clausifyMsSoFar
        // Nothing after this is bounded by `timeoutMs`, so publish the proof now as `UNCHECKED`, which must never
        // count as a checked refutation.
        if cfg.check && !cfg.clausifyOnly then
          val sNow = stats.get
          publish(Timing("UNCHECKED", clausifyMs, searchNanos.get / 1e6, reconstructNanos.get / 1e6,
                         givenProcessed = sNow.givenProcessed, derived = sNow.passiveEnqueued,
                         peakActive = sNow.peakActive, peakPassive = sNow.peakPassive,
                         clauses = clauseCount.get, freshSymbols = freshCount.get,
                         metrics = Some(ProofMetrics.of(proof))))
        val cs = System.nanoTime()
        val judgement = if cfg.check then Some(K.SCProofChecker.checkSCProof(proof)) else None
        val checkMs = if cfg.check then (System.nanoTime() - cs) / 1e6 else 0.0
        val sorry = judgement match
          case Some(K.SCProofCheckerJudgement.SCValidProof(_, us)) => us
          case _ => false
        // A `Sorry` is expected in clausify-only mode; anywhere else it makes a valid but worthless proof.
        val verdict =
          if judgement.exists(!_.isValid) then "BAD_PROOF"
          else if cfg.clausifyOnly then "CLAUSIFIED"
          else if sorry then "BAD_PROOF"
          else "REFUTED"
        // Keep the checker's message and failing step, so a bug can be located without rerunning the search.
        val detail = judgement match
          case Some(K.SCProofCheckerJudgement.SCInvalidProof(_, path, message)) =>
            s"step ${path.mkString(".")}: ${message.replace(',', ';').replace('\n', ' ').take(300)}"
          case _ =>
            if sorry && !cfg.clausifyOnly then "valid only via Sorry"
            else if !cfg.check then "unchecked"
            else ""
        Timing(
          verdict,
          clausifyMs, searchNanos.get / 1e6, reconstructNanos.get / 1e6, checkMs,
          metrics = Some(ProofMetrics.of(proof)), usesSorry = sorry,
          detail = detail
        )
      catch
        case nr: NonRefutation =>
          val cat = nr.outcome match
            case Clausal.Outcome.Saturated => "SATURATED"
            case Clausal.Outcome.Timeout => "TIMEOUT"
            case _ => "UNKNOWN"
          Timing(cat, clausifyMsSoFar, searchNanos.get / 1e6, reconstructNanos.get / 1e6)
        case _: InterruptedException => Timing("TIMEOUT", clausifyMsSoFar, searchNanos.get / 1e6, reconstructNanos.get / 1e6)
        // Keep what the prover threw, as for a rejected proof.
        case pe: ProverError =>
          val cause = Option(pe.getCause).getOrElse(pe)
          val where = cause.getStackTrace.headOption.fold("")(t => s" at ${t.getClassName.split('.').last}.${t.getMethodName}:${t.getLineNumber}")
          val what = s"${cause.getClass.getSimpleName}: ${Option(cause.getMessage).getOrElse("")}$where"
          // Running out of heap or stack is a resource limit, not a soundness failure, so it is not `BAD_PROOF`.
          if cause.isInstanceOf[OutOfMemoryError] || cause.isInstanceOf[StackOverflowError] then
            System.err.println(s"[exhausted] ${cause.getClass.getName}: ${cause.getMessage}")
            Timing("EXHAUSTED", clausifyMsSoFar, searchNanos.get / 1e6, reconstructNanos.get / 1e6, detail = what.replace(',', ';').replace('\n', ' ').take(300))
          else
            // The CSV gets one line, the log the trace.
            System.err.println(s"[bad-proof] ${cause.getClass.getName}: ${cause.getMessage}")
            cause.getStackTrace.take(12).foreach(t => System.err.println(s"[bad-proof]   at $t"))
            Timing("BAD_PROOF", clausifyMsSoFar, searchNanos.get / 1e6, reconstructNanos.get / 1e6, detail = what.replace(',', ';').replace('\n', ' ').take(300))
        case e: Throwable => Timing(s"CLAUSIFY_ERR(${e.getClass.getSimpleName})", clausifyMsSoFar, searchNanos.get / 1e6, reconstructNanos.get / 1e6)
    val s = stats.get
    base.copy(
      givenProcessed = s.givenProcessed, derived = s.passiveEnqueued,
      peakActive = s.peakActive, peakPassive = s.peakPassive,
      clauses = clauseCount.get, freshSymbols = freshCount.get
    )

  /**
   * Naming atoms and Skolem symbols in the prover's clause set, counted by the prefixes reserved in
   * `Clausification.GeneratedNames`, so that both clausifiers are measured the same way.
   */
  private def freshSymbolsOf(p: Problem): Int =
    val prefixes = Set(GeneratedNames.namingAtom, GeneratedNames.skolemFun)
    p.imports.iterator
      .flatMap(s => s.left.iterator ++ s.right.iterator)
      .flatMap(_.freeVariables)
      .collect { case v if prefixes(v.id.name) => v.id }
      .toSet
      .size

  /**
   * Clausify one problem both ways, solve, and report the kernel checker's verdict in full, for diagnosing a
   * `BAD_PROOF` row. Both clausifiers take a `Problem => SCProof`, so a non-refutation is fatal here.
   */
  def verifyOne(rel: String): Unit =
    val root: Option[File] = BenchUtil.tptpRootOrExplain()
    if root.isEmpty then return
    val f = new File(root.get, rel)
    val cprob = Prover.fromTptp(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
    def prover(p: Problem): K.SCProof =
      Clausal.prove(p).fold(o => throw new RuntimeException(s"expected a refutation, got $o"), identity)
    for (label, mk) <- Seq[(String, () => K.SCProof)](
        "uncertified" -> (() => UncertifiedClausifier.uncertifyClausal(cprob, prover)),
        "certified" -> (() => CertifiedClausifier.certifyClausal(cprob, prover))
      )
    do
      print(f"$rel%-18s $label%-12s ")
      try
        val proof = mk()
        val r = K.SCProofChecker.checkSCProof(proof)
        println(s"valid=${r.isValid}  conclusion=${proof.conclusion}  steps=${proof.steps.size} imports=${proof.imports.size}")
        r match
          case K.SCProofCheckerJudgement.SCInvalidProof(_, path, message) => println(s"    INVALID at step-path $path: $message")
          case _ => ()
      catch case e: Throwable => println(s"threw ${e.getClass.getSimpleName}: ${e.getMessage}")

  // ── summary ───────────────────────────────────────────────────────────────────────────────────────────────

  private def report(rows: Seq[Timing], total: Int): Unit =
    def count(pred: String => Boolean): Int = rows.count(r => pred(r.category))
    val refuted = count(_ == "REFUTED")
    println(
      s"\nrefuted=$refuted  saturated=${count(_ == "SATURATED")}  timeout=${count(_ == "TIMEOUT")}  " +
        s"hard_timeout=${count(_ == "HARD_TIMEOUT")}  bad_proof=${count(_ == "BAD_PROOF")}  " +
        s"exhausted=${count(_ == "EXHAUSTED")}  " +
        s"clausify_err=${count(_.startsWith("CLAUSIFY_ERR"))}  error=${count(_.startsWith("ERROR"))}  " +
        s"parse_err=${count(_ == "PARSE_ERR")}  skipped=${count(_ == "SKIPPED")}  " +
        (if count(_ == "CLAUSIFIED") > 0 then s"clausified=${count(_ == "CLAUSIFIED")}  " else "") + s"of $total"
    )
    val ran = rows.filter(r => ReachedProver(r.category))
    if ran.nonEmpty then
      val givenTotal = ran.map(_.givenProcessed.toLong).sum // one `Long` sum: an `Int` one overflows on big runs
      println(
        f"loop: given total=$givenTotal%d  avg=${givenTotal.toDouble / ran.size}%.0f  " +
          f"maxActive=${ran.map(_.peakActive).max}%d  maxPassive=${ran.map(_.peakPassive).max}%d  (over ${ran.size} runs that reached the prover)"
      )

    def phase(label: String, xs: Seq[Double]): Unit =
      if xs.nonEmpty then println(f"  $label%-9s total=${xs.sum}%8.0f  avg=${xs.sum / xs.size}%7.1f  median=${median(xs)}%7.1f  max=${xs.max}%8.1f ms")

    val solved = rows.filter(_.category == "REFUTED")
    if solved.nonEmpty then
      println(s"\nphase times over the $refuted REFUTED problems:")
      phase("clausify", solved.map(_.clausifyMs))
      phase("search", solved.map(_.searchMs))
      phase("reconstruct", solved.map(_.reconstructMs))
      phase("check", solved.map(_.checkMs))
    // Clausification runs regardless of the prover's verdict, so it is worth summing over every attempt.
    val attempted = rows.filter(r => ReachedProver(r.category) || r.category.startsWith("CLAUSIFY_ERR"))
    if attempted.nonEmpty then
      println(s"\nclausify time over all ${attempted.size} attempted (any verdict):")
      phase("clausify", attempted.map(_.clausifyMs))
