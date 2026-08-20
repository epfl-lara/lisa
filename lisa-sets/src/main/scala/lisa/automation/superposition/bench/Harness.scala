package lisa.automation.superposition
package bench

import java.io.File
import scala.util.{Try, Success, Failure, Using}

import lisa.utils.K
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.{CertifiedClausifier, UncertifiedClausifier}
import lisa.automation.Problem
import BenchUtil.{withTimeout, median}

/**
 * Runs a dataset through the whole pipeline: clausify, refute, kernel-check the composed proof. A `bad_proof`
 * row is therefore a reconstruction or composition bug. The clausifiers take a `Problem => SCProof`, so the
 * prover is called mid-descent and is timed inside its own closure. Certified and uncertified produce the same
 * clauses, so the difference between the two modes is the cost of building the proof.
 *
 * The three dataset objects ([[Evaluation]], [[FofEvaluation]], [[EqFofEvaluation]]) differ only in the list
 * they draw from. Requires `TPTP` to point at the problem library.
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

  /** Every problem path in the list, relative to the TPTP root, in file order. */
  def allProblems: Vector[String] = problems.all

  /** A reproducible sample of `n` problems drawn with `seed`; an `n` past the list returns all of it. */
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = problems.sample(n, seed)

  // ── configuration ─────────────────────────────────────────────────────────────────────────────────────────

  /** One run's settings. `seed`/`n` choose the sample, `timeoutMs` and `opts.maxGiven` bound each problem,
    * `maxSize` skips problems whose summed formula size would blow up clausification, and `certified` picks
    * the clausifier. `raw` is the command line that produced this, handed to a forked child unchanged. */
  final case class Config(seed: Long = 42, n: Int = 100, timeoutMs: Long = 15000L, maxSize: Int = 50000,
                          certified: Boolean = true,
                          opts: SearchOptions = SearchOptions(maxGiven = 100000),
                          raw: Seq[String] = Nil):
    def mode: String = if certified then "certified" else "uncertified"

  /** Parse `key=value` arguments. Recognised keys: `seed`, `n`, `timeout`, `given`, `size`, `mode` (`cert` or
    * `uncert`), and any search flag named by [[withFlag]], each taking `on`/`off`. */
  private def parse(args: Seq[String]): Config =
    args.foldLeft(Config(raw = args)) { (c, arg) =>
      val (key, value) = arg.span(_ != '=') match { case (k, v) => (k, v.drop(1)) }
      def flag: Boolean = value.toLowerCase match
        case "on" | "true" | "1"   => true
        case "off" | "false" | "0" => false
        case other                 => sys.error(s"'$key' takes on|off, got '$other'")
      key match
        case "seed"    => c.copy(seed = value.toLong)
        case "n"       => c.copy(n = value.toInt)
        case "timeout" => c.copy(timeoutMs = value.toLong)
        case "given"   => c.copy(opts = c.opts.copy(maxGiven = value.toInt))
        case "size"    => c.copy(maxSize = value.toInt)
        case "mode"    => c.copy(certified = value.toLowerCase != "uncert")
        case _         => c.copy(opts = withFlag(c.opts, key, flag))
    }

  /** The search flags the command line can set by name. Everything else keeps its [[SearchOptions]] default. */
  private def withFlag(o: SearchOptions, key: String, on: Boolean): SearchOptions = key match
    case "equality"      => o.copy(equality = on)
    case "superposition" => o.copy(superposition = on)
    case "fwdSubs"       => o.copy(forwardSubsumption = on)
    case "bwdSubs"       => o.copy(backwardSubsumption = on)
    case "fwdUD"         => o.copy(forwardUnitDeletion = on)
    case "bwdUD"         => o.copy(backwardUnitDeletion = on)
    case "fwdSR"         => o.copy(forwardSubsumptionResolution = on)
    case "bwdSR"         => o.copy(backwardSubsumptionResolution = on)
    case "fwdDemod"      => o.copy(forwardDemodulation = on)
    case "bwdDemod"      => o.copy(backwardDemodulation = on)
    case "cond"          => o.copy(condensation = on)
    case "genSimplify"   => o.copy(forwardSimplifyAtGeneration = on)
    case other           => sys.error(s"unknown option '$other'")

  // ── CLI ───────────────────────────────────────────────────────────────────────────────────────────────────

  def main(args: Array[String]): Unit = args.toSeq match
    // The child half of the forked path: solve exactly one problem, print one `RESULT` line, exit. It re-parses
    // the parent's own arguments, so the two runs are configured by the same code.
    case "solve1" +: file +: rest => solveChild(file, rest)
    case "sample" +: rest         =>
      sample(rest.lift(0).map(_.toInt).getOrElse(100), rest.lift(1).map(_.toLong).getOrElse(42L)).foreach(println)
    case "verify" +: rest         => rest.foreach(verifyOne)
    case "files" +: list +: rest  => runFiles(list, parse(rest))
    case rest                     => benchmark(parse(rest))

  /** Draw a seeded sample and run each problem. */
  def benchmark(cfg: Config): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    val picked = sample(cfg.n, cfg.seed)
    println(s"list=${problems.describe} (${allProblems.size} problems), seed=${cfg.seed}, n=${picked.size}, " +
      s"timeout=${cfg.timeoutMs}ms, maxGiven=${cfg.opts.maxGiven}, maxSize=${cfg.maxSize}, mode=${cfg.mode}, " +
      s"equality=${cfg.opts.equality}, ${BenchUtil.isolationBanner}")
    run(picked, tptpRoot.get, cfg)

  /** Run an explicit list of TPTP-root-relative paths, one per line, with no sampling and no size guard. */
  private def runFiles(listPath: String, cfg0: Config): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    val paths = Using(scala.io.Source.fromFile(listPath))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get
    val cfg = cfg0.copy(maxSize = Int.MaxValue)
    println(s"files=$listPath (${paths.size} problems), timeout=${cfg.timeoutMs}ms, maxGiven=${cfg.opts.maxGiven}, " +
      s"mode=${cfg.mode}, ${BenchUtil.isolationBanner}")
    run(paths, tptpRoot.get, cfg)

  private def run(paths: Vector[String], tptpRoot: File, cfg: Config): Unit =
    BenchUtil.resetAbandoned() // this run's contamination count starts here
    println(f" ${"PROBLEM"}%-19s ${"HYP"}%4s ${"CJ"}%3s  ${"RESULT"}%-12s ${"clausify"}%10s ${"prover"}%10s ${"check"}%9s ${"given"}%9s")
    report(paths.map(rel => solveRow(new File(tptpRoot, rel), cfg)), paths.size)

  // ── one problem ───────────────────────────────────────────────────────────────────────────────────────────

  /** Per-problem outcome and where the wall-clock went: `clausifyMs` (everything outside the prover call),
    * `proverMs` (search and reconstruction), `checkMs` (the kernel check), plus the loop-scale counters.
    * `contaminated` marks a row that ran while an abandoned worker was still alive, whose timings and often
    * whose verdict say more about that thread than about this problem. */
  private final case class Timing(category: String, clausifyMs: Double = 0.0, proverMs: Double = 0.0, checkMs: Double = 0.0,
                                  givenProcessed: Int = 0, peakActive: Int = 0, peakPassive: Int = 0,
                                  contaminated: Boolean = false, detail: String = "")

  /** Categories whose problem reached the prover, i.e. clausified without error. */
  private val ReachedProver: Set[String] = Set("REFUTED", "SATURATED", "TIMEOUT", "BAD_PROOF")

  /** Solve one problem and print its row, in its own JVM when [[BenchUtil.forkEnabled]], else in-process. */
  private def solveRow(f: File, cfg: Config): Timing =
    val name = f.getName
    if !f.exists then { println(f" $name%-19s ${"-- file not found --"}"); return Timing("MISSING") }
    // Sampled *before* the run: a worker this problem abandons contaminates its successors, not itself. In
    // fork mode nothing is ever abandoned, since the child is killed, so this stays false throughout.
    val dirty = BenchUtil.abandonedWorkers > 0
    val (hyps, cj, res0) =
      if BenchUtil.forkEnabled then solveForked(f, cfg)
      else solveLocal(f, cfg, outerTimeout = true)
    val res = res0.copy(contaminated = dirty)
    val mark = if dirty then "!" else " "
    val h = if hyps < 0 then "?" else hyps.toString
    val detail = if res.detail.isEmpty then "" else s"  (${res.detail})"
    println(f"$mark$name%-19s $h%4s $cj%3s  ${res.category}%-12s ${res.clausifyMs}%10.1f ${res.proverMs}%10.1f ${res.checkMs}%9.1f ${res.givenProcessed}%9d$detail")
    res

  /** Run this problem in a fresh JVM and read back its one `RESULT` line. A child that printed none was killed
    * on timeout or died on a fatal error, and the two are distinguishable. */
  private def solveForked(f: File, cfg: Config): (Int, String, Timing) =
    val outcome = BenchUtil.runForked(childMainClass, Seq("solve1", f.getPath) ++ cfg.raw, cfg.timeoutMs + 5000L)
    outcome.resultLine.flatMap(decodeRow).getOrElse(
      (-1, "?", Timing(if outcome.timedOut then "HARD_TIMEOUT" else "PROVER_CRASH", detail = outcome.crashDetail)))

  /** Child entry: solve one problem, print one machine-readable line, exit. No outer timeout, since the
    * parent's `destroyForcibly` is the hard cap and the loop still honours `timeoutMs` cooperatively. */
  private def solveChild(file: String, args: Seq[String]): Unit =
    val (hyps, cj, t) = solveLocal(new File(file), parse(args), outerTimeout = false)
    println(encodeRow(hyps, cj, t))

  // Plain `toString`/`toDouble` rather than the `f` interpolator: `%f` formats in the default locale, writing
  // `0,3` where the parser expects `0.3`.
  private def encodeRow(hyps: Int, cj: String, t: Timing): String =
    Seq(t.category, hyps.toString, cj, t.clausifyMs.toString, t.proverMs.toString, t.checkMs.toString,
      t.givenProcessed.toString, t.peakActive.toString, t.peakPassive.toString, t.detail).mkString(BenchUtil.ResultPrefix, "\t", "")

  private def decodeRow(line: String): Option[(Int, String, Timing)] =
    val p = line.stripPrefix(BenchUtil.ResultPrefix).split('\t')
    if p.length < 9 then None
    else Try((p(1).toInt, p(2), Timing(p(0), p(3).toDouble, p(4).toDouble, p(5).toDouble,
      p(6).toInt, p(7).toInt, p(8).toInt, detail = p.lift(9).getOrElse("")))).toOption

  /** Parse, clausify and solve one problem in this JVM. `outerTimeout` adds the thread-based wall-clock guard,
    * wanted when this *is* the run (`LISA_FORK=0`), redundant in a child whose parent will kill it. */
  private def solveLocal(f: File, cfg: Config, outerTimeout: Boolean): (Int, String, Timing) =
    if !f.exists then return (-1, "?", Timing("MISSING"))
    // Catch `Throwable`, not just `NonFatal`: the recursive TPTP parser can `StackOverflowError` on very
    // deeply-nested formulas, which would otherwise kill the whole run.
    (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
     catch { case e: Throwable => Failure(e) }) match
      case Failure(e) => (-1, "?", Timing("PARSE_ERR", detail = e.getClass.getSimpleName))
      case Success(parsed) =>
        val cprob = Prover.fromTptp(parsed)
        val hyps = cprob.hypotheses.size
        val cj = if cprob.conjecture.isDefined then "y" else "-"
        val size = cprob.size
        if size > cfg.maxSize then (hyps, cj, Timing("SKIPPED", detail = s"|F|=$size > ${cfg.maxSize}"))
        else if !outerTimeout then
          (hyps, cj, try solveOne(cprob, cfg) catch { case e: Throwable => Timing(s"ERROR(${e.getClass.getSimpleName})") })
        else
          (hyps, cj, withTimeout(cfg.timeoutMs + 5000L)(solveOne(cprob, cfg)) match
            case Some(Success(t)) => t
            case Some(Failure(e)) => Timing(s"ERROR(${e.getClass.getSimpleName})")
            case None             => Timing("HARD_TIMEOUT"))

  /** A non-refutation thrown by the prover to abort the clausification it was called from. */
  private final class NonRefutation(val outcome: Clausal.Outcome) extends RuntimeException
  /** A throw from the prover closure, kept distinct from a clausification throw so that it is categorised
    * `BAD_PROOF` rather than `CLAUSIFY_ERR`. */
  private final class ProverError(cause: Throwable) extends RuntimeException(cause)

  /** Run the pipeline once, timing each phase and recording the loop-scale stats. */
  private def solveOne(cprob: Problem, cfg: Config): Timing =
    val proverNanos = new java.util.concurrent.atomic.AtomicLong(0L)
    val stats = new java.util.concurrent.atomic.AtomicReference[Discount.LoopStats](Discount.LoopStats(0, 0, 0, 0))
    val prover: Problem => K.SCProof = p =>
      val ps = System.nanoTime()
      try
        Clausal.prove(p, cfg.opts.copy(maxMillis = cfg.timeoutMs, onStats = stats.set)) match
          case Right(proof) => proof
          case Left(other)  => throw new NonRefutation(other)
      catch
        case nr: NonRefutation        => throw nr // a decided non-refutation: propagate to the SATURATED/TIMEOUT arm
        case ie: InterruptedException => throw ie // hard-timeout interrupt: propagate to the TIMEOUT arm
        case e: Throwable             => throw new ProverError(e)
      finally proverNanos.addAndGet(System.nanoTime() - ps)
    val t0 = System.nanoTime()
    def clausifyMsSoFar: Double = (System.nanoTime() - t0 - proverNanos.get) / 1e6
    val base: Timing =
      try
        val proof =
          if cfg.certified then CertifiedClausifier.certifyClausal(cprob, prover)
          else UncertifiedClausifier.uncertifyClausal(cprob, prover)
        val clausifyMs = clausifyMsSoFar
        val cs = System.nanoTime()
        val valid = K.SCProofChecker.checkSCProof(proof).isValid
        Timing(if valid then "REFUTED" else "BAD_PROOF", clausifyMs, proverNanos.get / 1e6, (System.nanoTime() - cs) / 1e6)
      catch
        case nr: NonRefutation =>
          val cat = nr.outcome match
            case Clausal.Outcome.Saturated => "SATURATED"
            case Clausal.Outcome.Timeout   => "TIMEOUT"
            case _                         => "UNKNOWN"
          Timing(cat, clausifyMsSoFar, proverNanos.get / 1e6)
        case _: InterruptedException => Timing("TIMEOUT", clausifyMsSoFar, proverNanos.get / 1e6)
        case _: ProverError          => Timing("BAD_PROOF", clausifyMsSoFar, proverNanos.get / 1e6)
        case e: Throwable            => Timing(s"CLAUSIFY_ERR(${e.getClass.getSimpleName})", clausifyMsSoFar, proverNanos.get / 1e6)
    val s = stats.get
    base.copy(givenProcessed = s.givenProcessed, peakActive = s.peakActive, peakPassive = s.peakPassive)

  /** Clausify one problem both ways, solve, and report the kernel checker's verdict in full, for diagnosing a
    * `BAD_PROOF` row. Both clausifiers take a `Problem => SCProof`, so a non-refutation is fatal here. */
  def verifyOne(rel: String): Unit =
    val root: Option[File] = BenchUtil.tptpRootOrExplain()
    if root.isEmpty then return
    val f = new File(root.get, rel)
    val cprob = Prover.fromTptp(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
    def prover(p: Problem): K.SCProof =
      Clausal.prove(p).fold(o => throw new RuntimeException(s"expected a refutation, got $o"), identity)
    for (label, mk) <- Seq[(String, () => K.SCProof)](
      "uncertified" -> (() => UncertifiedClausifier.uncertifyClausal(cprob, prover)),
      "certified"   -> (() => CertifiedClausifier.certifyClausal(cprob, prover))
    ) do
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
        s"clausify_err=${count(_.startsWith("CLAUSIFY_ERR"))}  error=${count(_.startsWith("ERROR"))}  " +
        s"parse_err=${count(_ == "PARSE_ERR")}  skipped=${count(_ == "SKIPPED")}  of $total"
    )
    // Printed before the numbers, not after: they are the thing being called into question.
    val warning = BenchUtil.contaminationWarning
    if warning.nonEmpty then
      println(warning)
      println(s"   ${rows.count(_.contaminated)} of $total row${if total == 1 then "" else "s"} ran after that " +
        "point and are marked `!` above.")

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
      phase("prover",   solved.map(_.proverMs))
      phase("check",    solved.map(_.checkMs))
    // Clausification runs regardless of the prover's verdict, so it is worth summing over every attempt.
    val attempted = rows.filter(r => ReachedProver(r.category) || r.category.startsWith("CLAUSIFY_ERR"))
    if attempted.nonEmpty then
      println(s"\nclausify time over all ${attempted.size} attempted (any verdict):")
      phase("clausify", attempted.map(_.clausifyMs))
