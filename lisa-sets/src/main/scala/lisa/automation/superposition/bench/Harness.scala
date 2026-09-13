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
 * `mode=uncert` is a different pipeline rather than a flag on this one: it clausifies without a certificate,
 * searches, and prints the refutation as TSTP, which is what the prover does at CASC. It builds no kernel
 * proof and checks nothing, so the difference between the two modes is the whole cost of certification. The
 * two clausifiers produce the same clauses, so nothing else varies between them.
 *
 * A dataset object such as [[FofEvaluation]] names the list it draws from and nothing else. Requires `TPTP` to
 * point at the problem library.
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
      // Run the kernel check, or stop at the reconstructed proof. Off measures what the certified pipeline
      // answers rather than what it answers and checks inside one budget: checking is not bounded by
      // `timeoutMs`, so a proof whose check outlasts the budget left costs its problem a verdict entirely.
      // A `check=off` row still carries the proof's metrics, but `uses_sorry` is false because nothing
      // looked, so the soundness counts of such a run mean nothing.
      check: Boolean = true,
      clausifier: ClausifierOptions = ClausifierOptions(),
      certified: Boolean = true,
      opts: SearchOptions = SearchOptions(maxGiven = 100000),
      // Where the listed problems live, when that is not the TPTP library: the CASC problems are scrambled
      // copies (implications reversed, conjuncts permuted) and must be run as issued, not as the library has
      // them. `$TPTP` is still required either way, since a problem's `include('Axioms/…')` resolves against
      // it once the lookup beside the problem file fails.
      problemRoot: Option[String] = None,
      // The CSV's `problem` column, when the file cannot supply it: StarExec copies every benchmark to
      // `theBenchmark.p`, so the name has to be passed in or all 400 rows look alike.
      problemName: String = "",
      dataset: String = "", //   the CSV's `dataset` column, set by the driver
      configName: String = "", //  the CSV's `config` column, naming this point of the matrix
      strategy: String = "", //  the CSV's `strategy` column, empty for a single-strategy run
      csvOut: Option[String] = None,
      // Print the TSTP derivation, as CASC wants. Only the single-problem entry point sets it: a batch run
      // would build hundreds of derivations to discard them, and bury its own output under the ones it kept.
      tstpOut: Boolean = false,
      // Treat `timeoutMs` as a wall-clock budget for this whole JVM, parsing and start-up included, rather
      // than as a budget for the search alone. Set only where one JVM handles one problem.
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
        // The hypothesis count below which SInE keeps everything, so it decides *whether* selection runs at
        // all rather than how hard it prunes. It is here because raising it from 32 to 500 turned selection
        // off for every problem between those counts -- 124 of the CASC 400 -- and cost seven problems the
        // competition entry had solved, three of them in under twelve seconds. Which threshold is right is a
        // measurement rather than a revert: SInE is incomplete, so pruning can also drop an axiom the proof
        // needed, and this key is what lets `e5` put the two settings against each other.
        // Adjusts a configuration that exists; it does not create one. `sineTol` and `sineDepth` above take
        // the other choice and switch selection on where a strategy had none, which for this key would wreck
        // the experiment it was added for: `balanced` runs unfiltered by design, so `sineMin=32` on it would
        // not lower a floor but enable SInE outright, and the A/B would be measuring two changes at once. It
        // did exactly that on SEV609+1 -- 2900 hypotheses, far above either floor, "recovered" by `balanced`,
        // which is selection appearing rather than a threshold moving.
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
   * One problem, for a cluster that schedules the problems itself: writes this run's CSV row into `outDir` and
   * prints an SZS status line.
   *
   * StarExec invokes a run script per (solver configuration, benchmark) pair with the problem as `$1` and a
   * preserved output directory as `$2`, and classifies the outcome by reading an SZS status off stdout. So the
   * two halves are both needed: the status for the cluster's own bookkeeping, and the row for everything the
   * paper measures beyond solved-or-not.
   *
   * '''In-process''', unlike every other entry point here: the harness normally forks a JVM per problem to keep
   * a runaway one from taking resources from its successors, but StarExec already isolates each pair, and the fork
   * would put a second JVM start inside the measured budget and confuse its resource accounting.
   */
  private def runOne(file: String, outDir: String, cfg0: Config): Unit =
    val f = new File(file)
    val out = new File(outDir)
    out.mkdirs()
    val cfg = cfg0.copy(maxSize = Int.MaxValue, csvOut = Some(new File(out, "result.csv").getPath), tstpOut = true, wallBudget = true)
    // The cluster names every benchmark `theBenchmark.p`, so the file cannot identify the problem. `problem=`
    // carries the real name when the caller knows it; the file name is only a fallback.
    val name = if cfg.problemName.nonEmpty then cfg.problemName else f.getName

    // A row even when the run is killed from outside. StarExec enforces its own limits and sends SIGTERM, and
    // a pair killed that way otherwise returns no CSV at all — losing `given`, `derived` and the phase times
    // for exactly the unsolved problems, which is what `e3-given` is built on. A shutdown hook cannot catch
    // SIGKILL, so this is a best effort, but SIGTERM comes first and is what the limits actually send.
    val written = new java.util.concurrent.atomic.AtomicBoolean(false)
    Runtime.getRuntime.addShutdownHook(new Thread(() =>
      if written.compareAndSet(false, true) then
        writeCsv(cfg.csvOut.get, Vector((name, Timing("KILLED", detail = "killed before finishing"))), cfg)
        println(s"% SZS status Timeout for $name")
    ))

    val (hyps, cj, res) = solveLocal(f, cfg, outerTimeout = true)
    val timing = res.copy(hypotheses = hyps) //  as `solveRow` does; `e5` splits on this column
    val hasConjecture = cj == "y"
    // The SZS ontology distinguishes a refuted conjecture from a refuted axiom set, and satisfiable likewise;
    // a budget that ran out is `Timeout`, and anything else is `GaveUp` rather than a claim we cannot support.
    val szs = timing.category match
      case "REFUTED" => if hasConjecture then "Theorem" else "Unsatisfiable"
      // A saturation is `GaveUp`, never `(Counter)Satisfiable`, which is [[CascProver]]'s rule and has to be
      // this one too: SInE selection drops axioms, so the search that saturated may have saturated a strictly
      // weaker problem, and claiming its conjecture underivable would be a wrong answer rather than a missing
      // one. The CSV still records `SATURATED`, so the analysis keeps the distinction the status line drops.
      case "SATURATED" => "GaveUp"
      case "CLAUSIFIED" => "GaveUp" //         clausify-only: nothing was proved, by construction
      case "TIMEOUT" | "HARD_TIMEOUT" => "Timeout"
      case _ => "GaveUp"
    if written.compareAndSet(false, true) then
      writeCsv(cfg.csvOut.get, Vector((name, timing)), cfg)
      println(s"% SZS status $szs for $name")
      // The derivation follows its status line, as CASC expects. Only the uncertified path produces one: the
      // certified path's proof is a kernel proof, which is checked rather than printed.
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
   * One row per problem. A quantity this run could not produce is written **empty**, never zero, so that an
   * aggregate cannot silently average "not measured" as "measured as zero": a problem that never reached the
   * prover has no clause count, and one that built no proof has no sizes.
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
          // Reconstruction and checking are reported only when a kernel proof was actually built, which is
          // what `metrics` being present means. The uncertified path builds none by design, so a `0.000` here
          // would read as "reconstructed, instantly" rather than "never reconstructed".
          if m.isDefined then f"${t.reconstructMs}%.3f" else "",
          if m.isDefined then f"${t.checkMs}%.3f" else "",
          // The loop counters default to 0, which for a problem that never reached the prover would read as
          // "searched and derived nothing" rather than "did not search".
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
      // Hypotheses the problem carries. In the CSV because `e5` splits on it: SInE keeps everything below
      // `SineConfig.minAxioms`, so an on/off comparison is only meaningful above that count.
      hypotheses: Int = -1,
      clauses: Int = -1, //         clauses handed to the prover; -1 when it was never reached
      freshSymbols: Int = -1, //    naming atoms and Skolem symbols in those clauses
      metrics: Option[ProofMetrics] = None, //  present exactly when a proof was built
      usesSorry: Boolean = false,
      detail: String = "",
      // The TSTP derivation, on the uncertified path, which produces one instead of a kernel proof. Not a CSV
      // column: it is many lines of TPTP, and only the single-problem entry point prints it — a batch run
      // would bury its own output under hundreds of derivations.
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
    // `publish` prints an intermediate row the moment the proof exists, before the kernel check, which has no
    // deadline of its own. The parent reads the *last* `RESULT` line, so the final row replaces it when the
    // check finishes; when the check outlasts the budget and the child is killed, the intermediate row is what
    // survives, and it says the problem was refuted rather than nothing at all.
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
        // Named, not positional: this decodes a wire format whose field order is fixed, into a record whose
        // field order is not, and a new field in the middle of `Timing` silently reassigns every argument
        // after it. `hypotheses` is absent here on purpose -- it travels as its own field, `p(1)`, and
        // `solveRow` puts it back on the result.
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
        // Parsing is part of the wall clock, so it has to come out of the budget. On the single-problem entry
        // point the caller's limit is a wall-clock limit on the whole process, and this JVM handles exactly
        // one problem, so its uptime is what has already been spent: JVM start-up plus reading a file that,
        // on a corpus like CSR or SEV, is a hundred thousand formulas deep. Timing the search from *after*
        // that put the answer past the caller's deadline on 202 of 400 problems, whose workers were then
        // killed with nothing to report but a `KILLED` row.
        //
        // Only here: the batch entry points reuse one JVM across problems, where uptime is cumulative and
        // would shrink every later problem's budget to nothing.
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
   * The uncertified pipeline: clausify without a certificate, search, and print the refutation as TSTP — what
   * the prover does at CASC, and what `e1a` measures.
   *
   * No kernel proof is built and none is checked, so `reconstructMs` and `checkMs` are absent rather than
   * zero, and there are no proof-size metrics: there is no proof object to measure. That absence is the point
   * of the experiment. Against `e1b`, which certifies the clausification, reconstructs the refutation and
   * kernel-checks the composition, the difference is the whole cost of certification; running this path
   * through the kernel too — which is what it used to do — would have measured only the clausification
   * certificate and reported it as the cost of certification.
   *
   * [[Prover.proveTstp]] is the same entry point [[CascProver]] uses, called with the same TSTP printer, so
   * this really is the competition configuration and not a reconstruction of it.
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
            // Captured rather than printed straight out: the SZS status line belongs before the derivation,
            // and only the caller knows the status.
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
          // Same distinction the certified path draws: running out of heap or stack is a resource limit and
          // not a defect, and must not be counted as one.
          val cat = if e.isInstanceOf[OutOfMemoryError] || e.isInstanceOf[StackOverflowError] then "EXHAUSTED" else s"ERROR(${e.getClass.getSimpleName})"
          Timing(cat, clausifyMs, searchMs, detail = what.replace(',', ';').replace('\n', ' ').take(300))
    val s = stats.get
    base.copy(givenProcessed = s.givenProcessed, derived = s.passiveEnqueued, peakActive = s.peakActive, peakPassive = s.peakPassive)

  /**
   * Run the pipeline once, timing each phase and recording the loop-scale stats.
   */
  private def solveOne(cprob: Problem, cfg: Config, parsed: lisa.tptp.TptpProblem, name: String,
                       publish: Timing => Unit = _ => ()): Timing =
    // The uncertified path is a different pipeline, not the certified one with a flag flipped: it builds no
    // kernel proof at all and so has nothing to check. See [[solveUncertified]].
    if !cfg.certified && !cfg.clausifyOnly then return solveUncertified(cprob, cfg, parsed, name)
    val searchNanos = new java.util.concurrent.atomic.AtomicLong(0L)
    val reconstructNanos = new java.util.concurrent.atomic.AtomicLong(0L)
    val clauseCount = new java.util.concurrent.atomic.AtomicInteger(-1)
    val freshCount = new java.util.concurrent.atomic.AtomicInteger(-1)
    def proverNanos: Long = searchNanos.get + reconstructNanos.get
    val stats = new java.util.concurrent.atomic.AtomicReference[Discount.LoopStats](Discount.LoopStats(0, 0, 0, 0))
    // `Clausal.prove` is inlined here rather than called, so that the search and the reconstruction of its
    // result are timed apart. Both accumulate, since the clausifier calls this closure as a continuation and
    // may call it more than once.
    // Takes the goal clauses as well as the problem: `certifyClausalGoal` supplies them, and the uncertified
    // path passes the same set, so both search with the same clause selection.
    val prover: (Problem, Set[Int]) => K.SCProof = (p, goal) =>
      try
        clauseCount.set(p.imports.size)
        freshCount.set(freshSymbolsOf(p))
        // Clausify-only: satisfy the prover contract with a `Sorry` and never search. What is then built and
        // checked is the clausification derivation alone, which is what the clausification variants are
        // compared on, and it costs nothing on problems no configuration could refute anyway.
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
        // Through `preprocessKernel`, so that SInE selection and orthologic normalisation happen here exactly
        // as they do in `Prover.proveKernel` and on the uncertified side in `proveTstp`. Calling the
        // clausifier directly skipped both: seven of the eight portfolio strategies set `sine` and four set
        // `orthologic`, so the certified runs were not running the strategies they were named for, and `e4`
        // and `e5` — whose whole content is switching those two on and off — measured nothing at all.
        val proof =
          if cfg.certified then Prover.preprocessKernel(cprob, cfg.opts)(CertifiedClausifier.certifyClausalGoal(_, prover, cfg.clausifier))
          else UncertifiedClausifier.uncertifyClausal(cprob, p => prover(p, Set.empty))
        val clausifyMs = clausifyMsSoFar
        // The proof exists and nothing after this point is bounded by `timeoutMs`. Publish what is known now,
        // under a verdict of its own: `UNCHECKED` is a refutation whose proof was built but never checked, and
        // must never be counted as a checked one.
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
        // In clausify-only mode nothing was proved, so the verdict says so: the proof is the clausification
        // derivation capped by a `Sorry`, and `usesSorry` is true by construction rather than by defect.
        // Anywhere else a `Sorry` makes the proof valid and worthless, so it counts as a bad proof rather than
        // a refutation: validity alone cannot tell a real refutation from a fabricated one.
        val verdict =
          if judgement.exists(!_.isValid) then "BAD_PROOF"
          else if cfg.clausifyOnly then "CLAUSIFIED"
          else if sorry then "BAD_PROOF"
          else "REFUTED"
        // A rejected proof is the one verdict that is useless without a reason: it says a reconstruction bug
        // exists but not where, and re-running to find out means reproducing a search that may have taken
        // minutes. So the checker's own message and the step it failed at are carried into the row.
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
        // Same reasoning as for a rejected proof: the verdict alone says a bug exists but not where, and
        // reproducing it means re-running a search. The cause is what the prover actually threw.
        case pe: ProverError =>
          val cause = Option(pe.getCause).getOrElse(pe)
          val where = cause.getStackTrace.headOption.fold("")(t => s" at ${t.getClassName.split('.').last}.${t.getMethodName}:${t.getLineNumber}")
          val what = s"${cause.getClass.getSimpleName}: ${Option(cause.getMessage).getOrElse("")}$where"
          // Running out of heap or stack is not a bad proof, and must not be counted as one: `BAD_PROOF` is
          // the verdict the artefact's T4 asserts is never non-zero, so filing an exhausted run under it
          // would report a soundness incident where there was only a resource limit. It is a separate
          // category, and one that says the run should be repeated with more of whatever it ran out of.
          if cause.isInstanceOf[OutOfMemoryError] || cause.isInstanceOf[StackOverflowError] then
            System.err.println(s"[exhausted] ${cause.getClass.getName}: ${cause.getMessage}")
            Timing("EXHAUSTED", clausifyMsSoFar, searchNanos.get / 1e6, reconstructNanos.get / 1e6, detail = what.replace(',', ';').replace('\n', ' ').take(300))
          else
            // The CSV gets one line; the log gets the trace. A prover error is always a bug and always rare,
            // so there is no cost to printing it, and without it the next reader repeats this investigation.
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
   * Naming atoms and Skolem symbols in the clause set handed to the prover, counted by the prefixes
   * `Clausification.GeneratedNames` reserves for them. Counted here rather than reported by the clausifier,
   * so that both clausifiers are measured the same way and neither needs instrumenting.
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
