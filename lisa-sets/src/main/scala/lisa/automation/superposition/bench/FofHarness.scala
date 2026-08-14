package lisa.automation.superposition
package bench

import java.io.File
import scala.util.{Try, Success, Failure, Using}

import lisa.utils.K
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.{Clausification, CertifiedClausifier, UncertifiedClausifier}
import lisa.automation.clausification.Clausification.problemSize
import BenchUtil.{withTimeout, toClausificationProblem, median}

/**
 * The shared FOF evaluation harness, parameterised by the dataset (`listFileName`) and the env var that
 * overrides its list location (`listEnvVar`). Both [[FofEvaluation]] (equality-free) and [[EqFofEvaluation]]
 * (equality-bearing) are thin configs over one instance of this, differing only in the dataset and its
 * documentation.
 *
 * Each sampled problem is parsed, run through the (un)certified clausifier
 * ([[CertifiedClausifier.certifyClausal]] vs [[UncertifiedClausifier.uncertifyClausal]], which give the same
 * clauses either way, so the delta measures the proof-building cost) with [[Clausal.proveOutcome]] as the
 * back-end, and on a refutation the composed proof is kernel-checked. The library-lemma statements remain
 * trusted imports until a tactic discharges them, so a `bad_proof` flags a composition/reconstruction bug.
 * The prover is timed from **inside** its closure, so `clausifyMs = total − prover` even though `certifyClausal`
 * calls the prover mid-descent (CPS).
 *
 * Needs the `TPTP` env var pointing at the TPTP root (the directory containing `Problems/`). CLI:
 * {{{
 *   [seed] [n] [timeoutMs] [maxGiven] [maxSize] [cert|uncert] [equality] [index|noindex]
 *   verify <rel>…        deep-check one problem (kernel-checker verdict in detail; for diagnosing BAD_PROOF)
 *   sample [n] [seed]    print the seeded draw's TPTP-root-relative paths (so an external prover runs the same set)
 *   files <listfile> …   run an explicit path list (one per line) through the same pipeline, no sampling
 * }}}
 * The `uncert` token skips certification; `off` skips all equality inferences (superposition, equality
 * resolution/factoring, demodulation); `noindex` runs superposition by linear scan instead of the fingerprint index.
 */
/** @param childMainClass the object whose `main` a forked child re-enters: the owning harness object, so it
  *                       reads the same problem list. See [[solveForked]]. */
final class FofHarness(listFileName: String, listEnvVar: String, childMainClass: String):

  private val problems: ProblemList = new ProblemList(listFileName, Some(listEnvVar))

  /** The full list of problem paths (relative to the TPTP root), in file order. Read once. */
  def allProblems: Vector[String] = problems.all

  /** A reproducible random sample of `n` problems drawn with `seed`; the same seed always picks the same
   *  sample, and an `n` past the list returns the whole shuffled list. */
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = problems.sample(n, seed)

  // ── CLI ───────────────────────────────────────────────────────────────────────────────────────────────────

  def main(args: Array[String]): Unit =
    // The child half of the forked path: solve exactly one problem, print one `RESULT` line, exit. Never
    // invoked by hand, since [[solveRow]] spawns it. Kept in this same main so the child needs no extra class.
    if args.headOption.contains("solve1") then { solveChild(args.drop(1)); return }
    if args.headOption.contains("verify") then { args.drop(1).foreach(verifyOne); return }
    if args.headOption.contains("sample") then
      sample(args.lift(1).map(_.toInt).getOrElse(100), args.lift(2).map(_.toLong).getOrElse(42L)).foreach(println)
      return
    if args.headOption.contains("files") then { runFiles(args.drop(1)); return }
    benchmark(
      seed = args.lift(0).map(_.toLong).getOrElse(42L),
      n = args.lift(1).map(_.toInt).getOrElse(100),
      timeoutMs = args.lift(2).map(_.toLong).getOrElse(15000L),
      maxGiven = args.lift(3).map(_.toInt).getOrElse(100000),
      maxSize = args.lift(4).map(_.toInt).getOrElse(50000),
      certified = args.lift(5).forall(_.toLowerCase != "uncert"), //           6th arg: cert|uncert
      equality = args.lift(6).forall(_.toLowerCase != "off"), //               7th arg: on|off
      fingerprintIndexing = args.lift(7).forall(_.toLowerCase != "noindex") // 8th arg: index|noindex
    )

  /**
   * Draw a seeded sample of `n` theorems and try to prove each within `timeoutMs`/`maxGiven` through the full
   * clausify + refute pipeline. Problems whose summed kernel formula size exceeds `maxSize` are skipped (they
   * blow up clausification memory/time). Prints a per-problem row and a category summary.
   */
  def benchmark(seed: Long = 42, n: Int = 100, timeoutMs: Long = 15000L, maxGiven: Int = 100000, maxSize: Int = 50000, certified: Boolean = true, equality: Boolean = true, fingerprintIndexing: Boolean = true): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    val picked = sample(n, seed)
    val mode = if certified then "certified" else "uncertified"
    println(s"list=${problems.describe} (${allProblems.size} problems), seed=$seed, n=${picked.size}, timeout=${timeoutMs}ms, maxGiven=$maxGiven, maxSize=$maxSize, mode=$mode, equality=$equality, index=$fingerprintIndexing, ${isolationBanner}")
    printHeader()
    val rows = picked.map(rel => solveRow(new File(tptpRoot.get, rel), timeoutMs, maxGiven, maxSize, certified, equality, fingerprintIndexing))
    report(rows, picked.size)

  /** Run an explicit list of TPTP-root-relative problem paths (read from `a(0)`, one per line) through the same
   *  pipeline as [[benchmark]], with no sampling. Args: `<listfile> [timeoutMs=15000] [maxGiven=100000]
   *  [cert|uncert=cert] [maxSize=∞]`; `maxSize` defaults to unbounded so the size guard is off. */
  private def runFiles(a: Array[String]): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    if a.isEmpty then { println("usage: files <listfile> [timeoutMs] [maxGiven] [cert|uncert] [maxSize]"); return }
    val paths = Using(scala.io.Source.fromFile(a(0)))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get
    val timeoutMs = a.lift(1).map(_.toLong).getOrElse(15000L)
    val maxGiven = a.lift(2).map(_.toInt).getOrElse(100000)
    val certified = a.lift(3).forall(_.toLowerCase != "uncert")
    val maxSize = a.lift(4).map(_.toInt).getOrElse(Int.MaxValue)
    val mode = if certified then "certified" else "uncertified"
    println(s"files=${a(0)} (${paths.size} problems), timeout=${timeoutMs}ms, maxGiven=$maxGiven, maxSize=$maxSize, mode=$mode, ${isolationBanner}")
    printHeader()
    val rows = paths.map(rel => solveRow(new File(tptpRoot.get, rel), timeoutMs, maxGiven, maxSize, certified))
    report(rows, paths.size)

  /** Which isolation the run used. It changes what the timings mean, so it belongs in the banner above them.
    * `fork` costs a JVM start-up per problem, so per-problem times on fast problems are dominated by it. */
  private def isolationBanner: String =
    if BenchUtil.forkEnabled then "isolation=fork (one JVM per problem; set LISA_FORK=0 for in-process)"
    else "isolation=thread (LISA_FORK=0; a runaway problem can poison later ones)"

  private def printHeader(): Unit =
    BenchUtil.resetAbandoned() // this run's contamination count starts here
    println(f" ${"PROBLEM"}%-19s ${"HYP"}%4s ${"CJ"}%3s  ${"RESULT"}%-12s ${"clausify"}%10s ${"prover"}%10s ${"check"}%9s ${"given"}%9s")

  /** Per-problem outcome plus a breakdown of where the wall-clock went: `clausifyMs` (everything in
   *  `certifyClausal`/`uncertifyClausal` outside the prover call), `proverMs` (Bridge search + reconstruction),
   *  `checkMs` (the final kernel check), and the loop-scale counters.
   *
   *  `contaminated` marks a row that ran while an earlier worker was still alive after being abandoned (see
   *  [[BenchUtil.abandonedWorkers]]): its timings, and often its verdict, say more about that thread than
   *  about this problem. */
  private final case class Timing(category: String, clausifyMs: Double = 0.0, proverMs: Double = 0.0, checkMs: Double = 0.0,
                                  givenProcessed: Int = 0, peakActive: Int = 0, peakPassive: Int = 0,
                                  contaminated: Boolean = false, detail: String = "")

  /** Deep-check one problem (path relative to the TPTP root): clausify both ways, solve, and report the
   *  kernel-checker verdict in detail, for diagnosing `BAD_PROOF`. */
  def verifyOne(rel: String): Unit =
    val tptpRoot = BenchUtil.tptpRootOrExplain().getOrElse(return)
    val f = new File(tptpRoot, rel)
    val cprob = toClausificationProblem(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
    for (label, mk) <- Seq[(String, () => K.SCProof)](
      "uncertified" -> (() => UncertifiedClausifier.uncertifyClausal(cprob, p => Clausal.prove(p))),
      "certified"   -> (() => CertifiedClausifier.certifyClausal(cprob, p => Clausal.prove(p)))
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

  /** Solve one problem and print its row, in its own JVM when [[BenchUtil.forkEnabled]], else in-process. */
  private def solveRow(f: File, timeoutMs: Long, maxGiven: Int, maxSize: Int, certified: Boolean, equality: Boolean = true, fingerprintIndexing: Boolean = true): Timing =
    val name = f.getName
    if !f.exists then { println(f" $name%-19s ${"-- file not found --"}"); return Timing("MISSING") }
    // Sampled *before* the run: a worker this problem abandons contaminates its successors, not itself. In
    // fork mode nothing is ever abandoned, since the child is killed, so this stays false throughout.
    val dirty = BenchUtil.abandonedWorkers > 0
    val (hyps, cj, res0) =
      if BenchUtil.forkEnabled then solveForked(f, timeoutMs, maxGiven, maxSize, certified, equality, fingerprintIndexing)
      else solveLocal(f, timeoutMs, maxGiven, maxSize, certified, equality, fingerprintIndexing, outerTimeout = true)
    val res = res0.copy(contaminated = dirty)
    printRow(name, hyps, cj, res, dirty)
    res

  private def printRow(name: String, hyps: Int, cj: String, t: Timing, dirty: Boolean): Unit =
    val mark = if dirty then "!" else " "
    val h = if hyps < 0 then "?" else hyps.toString
    val detail = if t.detail.isEmpty then "" else s"  (${t.detail})"
    println(f"$mark$name%-19s $h%4s $cj%3s  ${t.category}%-12s ${t.clausifyMs}%10.1f ${t.proverMs}%10.1f ${t.checkMs}%9.1f ${t.givenProcessed}%9d$detail")

  // ── forked execution ──────────────────────────────────────────────────────────────────────────────────────
  // The parent spawns one JVM per problem and reads back a single `RESULT` line. A child that never prints
  // one was killed on timeout or died on a fatal error, and the two are distinguishable, which is more than
  // the in-process path could manage, where both surfaced as `BAD_PROOF` (see the code review, §4.5).

  /** Run this problem in a fresh JVM. The child gets `timeoutMs + 5000` wall-clock before it is killed, the
    * same outer budget the in-process path allowed, but here the kill is real. */
  private def solveForked(f: File, timeoutMs: Long, maxGiven: Int, maxSize: Int, certified: Boolean, equality: Boolean, indexing: Boolean): (Int, String, Timing) =
    val argv = Seq("solve1", f.getPath, timeoutMs.toString, maxGiven.toString, maxSize.toString,
      if certified then "cert" else "uncert", if equality then "on" else "off", if indexing then "index" else "noindex")
    val outcome = BenchUtil.runForked(childMainClass, argv, timeoutMs + 5000L)
    outcome.resultLine.flatMap(decodeRow) match
      case Some(row) => row
      case None      => (-1, "?", Timing(if outcome.timedOut then "HARD_TIMEOUT" else "PROVER_CRASH", detail = outcome.crashDetail))

  /** Child entry: solve one problem, print one machine-readable line, exit. No outer timeout: the parent's
    * `destroyForcibly` is the hard cap, and `solveOne` still honours `timeoutMs` cooperatively. */
  private def solveChild(a: Array[String]): Unit =
    val (hyps, cj, t) = solveLocal(new File(a(0)), a(1).toLong, a(2).toInt, a(3).toInt,
      certified = a(4) != "uncert", equality = a(5) != "off", indexing = a(6) != "noindex", outerTimeout = false)
    println(encodeRow(hyps, cj, t))

  // Plain `toString`/`toDouble`, not the `f` interpolator: `%f` formats in the default locale, which writes
  // `0,3` where the parser expects `0.3`, a bug that would only appear on a machine configured differently
  // from the one this was written on.
  private def encodeRow(hyps: Int, cj: String, t: Timing): String =
    Seq(t.category, hyps.toString, cj, t.clausifyMs.toString, t.proverMs.toString, t.checkMs.toString,
      t.givenProcessed.toString, t.peakActive.toString, t.peakPassive.toString, t.detail).mkString(BenchUtil.ResultPrefix, "\t", "")

  private def decodeRow(line: String): Option[(Int, String, Timing)] =
    val p = line.stripPrefix(BenchUtil.ResultPrefix).split('\t')
    if p.length < 9 then None
    else Try((p(1).toInt, p(2), Timing(p(0), p(3).toDouble, p(4).toDouble, p(5).toDouble,
      p(6).toInt, p(7).toInt, p(8).toInt, detail = p.lift(9).getOrElse("")))).toOption

  /** Parse + clausify + solve one problem in this JVM. `outerTimeout` adds the thread-based wall-clock guard,
    * wanted when this *is* the run (`LISA_FORK=0`), redundant in a child whose parent will kill it. */
  private def solveLocal(f: File, timeoutMs: Long, maxGiven: Int, maxSize: Int, certified: Boolean,
                         equality: Boolean, indexing: Boolean, outerTimeout: Boolean): (Int, String, Timing) =
    if !f.exists then return (-1, "?", Timing("MISSING"))
    // Catch `Throwable`, not just `NonFatal`: the recursive TPTP parser can `StackOverflowError` on very
    // deeply-nested formulas (e.g. the parameterised LCL problems), which would otherwise kill the whole run.
    (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
     catch { case e: Throwable => Failure(e) }) match
      case Failure(e) => (-1, "?", Timing("PARSE_ERR", detail = e.getClass.getSimpleName))
      case Success(parsed) =>
        val cprob = toClausificationProblem(parsed)
        val hyps = cprob.hypotheses.size
        val cj = if cprob.conjecture.isDefined then "y" else "-"
        val fsize = problemSize(cprob)
        if fsize > maxSize then (hyps, cj, Timing("SKIPPED", detail = s"|F|=$fsize > $maxSize"))
        else if !outerTimeout then
          (hyps, cj, try solveOne(cprob, timeoutMs, maxGiven, certified, equality, indexing)
                     catch { case e: Throwable => Timing(s"ERROR(${e.getClass.getSimpleName})") })
        else
          val t = withTimeout(timeoutMs + 5000L)(solveOne(cprob, timeoutMs, maxGiven, certified, equality, indexing)) match
            case Some(Success(t)) => t
            case Some(Failure(e)) => Timing(s"ERROR(${e.getClass.getSimpleName})")
            case None             => Timing("HARD_TIMEOUT")
          (hyps, cj, t)

  /** A non-refutation ([[Bridge.Outcome]] `Saturated`/`Timeout`) thrown by the back-end to abort clausification. */
  private final class NonRefutation(val outcome: Bridge.Outcome) extends RuntimeException
  /** A throw from the prover/reconstruction closure (a proof-composition/reconstruction or search crash), kept
   *  distinct from a clausification throw so it is categorised `BAD_PROOF`, not `CLAUSIFY_ERR`. */
  private final class ProverError(cause: Throwable) extends RuntimeException(cause)

  /** Run the (un)certified pipeline once, timing each phase and recording the loop-scale stats. Runs on the
   *  worker thread inside [[BenchUtil.withTimeout]]. */
  private def solveOne(cprob: Clausification.Problem, timeoutMs: Long, maxGiven: Int, certified: Boolean, equality: Boolean = true, fingerprintIndexing: Boolean = true): Timing =
    val proverNanos = new java.util.concurrent.atomic.AtomicLong(0L)
    val stats = new java.util.concurrent.atomic.AtomicReference[Discount.LoopStats](Discount.LoopStats(0, 0, 0, 0))
    val prover: Clausification.Problem => K.SCProof = p =>
      val ps = System.nanoTime()
      try
        Clausal.proveOutcome(p, maxGiven, timeoutMs, SearchOptions(equality = equality, fingerprintIndexing = fingerprintIndexing), onStats = stats.set) match
          case Right(proof) => proof
          case Left(other)  => throw new NonRefutation(other)
      catch
        case nr: NonRefutation        => throw nr // a decided non-refutation: propagate to the SATURATED/TIMEOUT arm
        case ie: InterruptedException => throw ie // hard-timeout interrupt: propagate to the TIMEOUT arm
        case e: Throwable             => throw new ProverError(e) // prover/reconstruction crash ⇒ BAD_PROOF, not CLAUSIFY_ERR
      finally proverNanos.addAndGet(System.nanoTime() - ps)
    val t0 = System.nanoTime()
    def clausifyMsSoFar: Double = (System.nanoTime() - t0 - proverNanos.get) / 1e6
    val base: Timing =
      try
        val proof =
          if certified then CertifiedClausifier.certifyClausal(cprob, prover)
          else UncertifiedClausifier.uncertifyClausal(cprob, prover)
        val clausifyMs = clausifyMsSoFar
        val cs = System.nanoTime()
        val valid = K.SCProofChecker.checkSCProof(proof).isValid
        Timing(if valid then "REFUTED" else "BAD_PROOF", clausifyMs, proverNanos.get / 1e6, (System.nanoTime() - cs) / 1e6)
      catch
        case nr: NonRefutation =>
          val cat = nr.outcome match
            case Bridge.Outcome.Saturated => "SATURATED"
            case Bridge.Outcome.Timeout   => "TIMEOUT"
            case _                        => "UNKNOWN"
          Timing(cat, clausifyMsSoFar, proverNanos.get / 1e6)
        case _: InterruptedException => Timing("TIMEOUT", clausifyMsSoFar, proverNanos.get / 1e6)
        case _: ProverError          => Timing("BAD_PROOF", clausifyMsSoFar, proverNanos.get / 1e6) // reconstruction/prover throw
        case e: Throwable            => Timing(s"CLAUSIFY_ERR(${e.getClass.getSimpleName})", clausifyMsSoFar, proverNanos.get / 1e6)
    val s = stats.get
    base.copy(givenProcessed = s.givenProcessed, peakActive = s.peakActive, peakPassive = s.peakPassive)

  /** Aggregate the per-problem categories + phase timings into the summary. */
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

    // Throughput / scale over problems that reached the prover: total given clauses processed (the throughput
    // measure) and the peak active/passive sizes reached, summed and maxed across the sample.
    val ran = rows.filter(r => Set("REFUTED", "SATURATED", "TIMEOUT", "BAD_PROOF").contains(r.category))
    if ran.nonEmpty then
      println(
        f"loop: given total=${ran.map(_.givenProcessed.toLong).sum}%d  avg=${ran.map(_.givenProcessed).sum.toDouble / ran.size}%.0f  " +
          f"maxActive=${ran.map(_.peakActive).max}%d  maxPassive=${ran.map(_.peakPassive).max}%d  (over ${ran.size} runs that reached the prover)"
      )

    def phase(label: String, xs: Seq[Double]): Unit =
      if xs.nonEmpty then println(f"  $label%-9s total=${xs.sum}%8.0f  avg=${xs.sum / xs.size}%7.1f  median=${median(xs)}%7.1f  max=${xs.max}%8.1f ms")

    // Phase breakdown over the SOLVED problems (where all three phases ran to completion).
    val solved = rows.filter(_.category == "REFUTED")
    if solved.nonEmpty then
      println(s"\nphase times over the $refuted REFUTED problems:")
      phase("clausify", solved.map(_.clausifyMs))
      phase("prover",   solved.map(_.proverMs))
      phase("check",    solved.map(_.checkMs))
    // Clausification cost across EVERY attempted problem (it runs regardless of the prover's verdict).
    val attempted = rows.filter(r => Set("REFUTED", "SATURATED", "TIMEOUT", "BAD_PROOF").contains(r.category) || r.category.startsWith("CLAUSIFY_ERR"))
    if attempted.nonEmpty then
      println(s"\nclausify time over all ${attempted.size} attempted (any verdict):")
      phase("clausify", attempted.map(_.clausifyMs))
