package lisa.automation.superposition

import java.io.File
import java.util.concurrent.atomic.AtomicReference
import scala.util.{Try, Success, Failure, Using}

import lisa.utils.K
import lisa.tptp.{AnnotatedFormula, AnnotatedSequent}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.{Clausification, UncertifiedClausification}
import lisa.automation.clausification.ClausificationStressTest.problemSize

/**
 * The second evaluation dataset + harness: non-clausal (FOF), first-order, equality-free, arithmetic-free
 * TPTP **theorems** (`tptp-fof-fo-noeq-thm.txt`) — the analog of the clausal [[Evaluation]] set, selected the
 * very same way (by the TPTP `SPC` header: `FOF_THM_{RFO,EPR}_NEQ`) but **without** the already-clausal
 * restriction. The `CSR` (SUMO commonsense) domain is excluded: all 359 such problems include a giant
 * (30k–40k-line) numeric ontology whose long numeric-suffixed identifiers (`c_bcase_3235139646`) the TPTP
 * parser mishandles and which exceed any sane clausification size budget — leaving 944 clean FO theorems.
 * Each sampled problem is parsed, run through the certified clausifier
 * ([[Clausification.certifyClausal]]) with [[Clausal.prove]] as the back-end, and — on a refutation — the
 * composed proof is kernel-checked. Paths are relative to the TPTP root (e.g. `Problems/SYN/SYN048+1.p`).
 *
 * Needs the `TPTP` env var pointing at the TPTP root (the directory containing `Problems/`). Run:
 * {{{
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.FofEvaluation [seed] [n] [timeoutMs] [maxGiven] [maxSize] [cert|uncert] [equality]"
 * }}}
 * The 6th arg `uncert` skips certification; the 7th arg `off` skips all equality inferences (superposition,
 * equality resolution/factoring, demodulation) — this list is equality-free, so `off` measures their inert cost.
 * Every `REFUTED` is reconstructed and kernel-checked (the library-lemma statements remain trusted imports
 * until the tactic discharges them), so a `bad_proof` flags a composition/reconstruction bug.
 */
object FofEvaluation:

  /** The generated full FOF list file (paths relative to the TPTP root). */
  private val listFileName = "tptp-fof-fo-noeq-thm.txt"

  /** Locate the FOF problem list: `TPTP_FOF_LIST`, else source-relative candidates / the cwd. */
  private def locateListFile(): Option[File] =
    val candidates: List[File] =
      sys.env.get("TPTP_FOF_LIST").map(new File(_)).toList :::
        List(
          s"lisa-sets/src/main/scala/lisa/automation/superposition/$listFileName",
          s"src/main/scala/lisa/automation/superposition/$listFileName",
          listFileName
        ).map(new File(_))
    candidates.find(_.isFile)

  /** The full list of FOF problem paths (relative to the TPTP root), in file order. Read once. */
  lazy val allProblems: Vector[String] =
    val list = locateListFile().getOrElse(
      throw new java.io.FileNotFoundException(s"Could not find $listFileName (set TPTP_FOF_LIST or run from the repo root).")
    )
    Using(scala.io.Source.fromFile(list))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get

  /**
   * A reproducible random sample of `n` problems drawn with `seed` — the exact mechanism
   * [[Evaluation.benchmark]] uses for the clausal set (`Random(seed).shuffle(all).take(n)`). The same seed
   * always picks the same sample; an `n` larger than the list just returns the whole (shuffled) list.
   */
  def sample(n: Int = 100, seed: Long = 42): Vector[String] =
    new scala.util.Random(seed).shuffle(allProblems).take(n)

  // ── Benchmark ───────────────────────────────────────────────────────────────────────────────────────────

  def main(args: Array[String]): Unit =
    if args.headOption.contains("verify") then { args.drop(1).foreach(verifyOne); return }
    benchmark(
      seed = args.lift(0).map(_.toLong).getOrElse(42L),
      n = args.lift(1).map(_.toInt).getOrElse(100),
      timeoutMs = args.lift(2).map(_.toLong).getOrElse(15000L),
      maxGiven = args.lift(3).map(_.toInt).getOrElse(100000),
      maxSize = args.lift(4).map(_.toInt).getOrElse(50000),
      certified = args.lift(5).forall(_.toLowerCase != "uncert"), // 6th arg "uncert" ⇒ skip certification
      equality = args.lift(6).forall(_.toLowerCase != "off") //     7th arg "off" ⇒ skip all equality inferences
    )

  /**
   * Draw a seeded sample of `n` FOF theorems and try to prove each within `timeoutMs`/`maxGiven` through the
   * full clausify + refute pipeline. Problems whose summed kernel formula size exceeds `maxSize` are skipped
   * (they blow up clausification memory/time). `certified` selects [[Clausification.certifyClausal]] (build the
   * clausification proof) vs [[UncertifiedClausification.uncertifyClausal]] (pure clause computation, no proof)
   * — the same clauses either way, so the delta measures the proof-building cost. Prints a per-problem row and
   * a category summary.
   */
  def benchmark(seed: Long = 42, n: Int = 100, timeoutMs: Long = 15000L, maxGiven: Int = 100000, maxSize: Int = 50000, certified: Boolean = true, equality: Boolean = true): Unit =
    val tptpRoot: Option[File] = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if tptpRoot.isEmpty then
      println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/).")
      return
    val picked = sample(n, seed)
    val mode = if certified then "certified" else "uncertified"
    println(s"list=$listFileName (${allProblems.size} problems), seed=$seed, n=${picked.size}, timeout=${timeoutMs}ms, maxGiven=$maxGiven, maxSize=$maxSize, mode=$mode, equality=$equality")
    println(f"${"PROBLEM"}%-20s ${"HYP"}%4s ${"CJ"}%3s  ${"RESULT"}%-12s ${"clausify"}%10s ${"prover"}%10s ${"check"}%9s")
    val rows = picked.map(rel => solveRow(new File(tptpRoot.get, rel), timeoutMs, maxGiven, maxSize, certified, equality))
    report(rows, picked.size)

  /** Per-problem outcome plus a breakdown of where the wall-clock went: `clausifyMs` (the (un)certifying
   *  clausification, i.e. everything in `certifyClausal`/`uncertifyClausal` outside the prover call),
   *  `proverMs` (Bridge search + reconstruction), `checkMs` (the final kernel check). */
  private final case class Timing(category: String, clausifyMs: Double = 0.0, proverMs: Double = 0.0, checkMs: Double = 0.0)

  /** Deep-check one problem (path relative to the TPTP root): clausify both ways, solve, and report the
   *  kernel-checker verdict in detail — for diagnosing `BAD_PROOF`. */
  def verifyOne(rel: String): Unit =
    val tptpRoot = sys.env.get("TPTP").map(new File(_)).getOrElse { println("set TPTP"); return }
    val f = new File(tptpRoot, rel)
    val cprob = toClausificationProblem(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
    for (label, mk) <- Seq[(String, () => K.SCProof)](
      "uncertified" -> (() => UncertifiedClausification.uncertifyClausal(cprob, p => Clausal.prove(p))),
      "certified"   -> (() => Clausification.certifyClausal(cprob, p => Clausal.prove(p)))
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

  /** Parse + clausify + solve one problem, kernel-check any refutation, print a per-phase row. */
  private def solveRow(f: File, timeoutMs: Long, maxGiven: Int, maxSize: Int, certified: Boolean, equality: Boolean = true): Timing =
    val name = f.getName
    if !f.exists then { println(f"$name%-20s ${"-- file not found --"}"); Timing("MISSING") }
    else
      // Catch `Throwable`, not just `NonFatal`: the recursive TPTP parser can `StackOverflowError` on very
      // deeply-nested formulas (e.g. the parameterised LCL problems), which would otherwise kill the whole run.
      (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
       catch { case e: Throwable => Failure(e) }) match
        case Failure(e) =>
          println(f"$name%-20s ${"?"}%4s ${"?"}%3s  ${"PARSE_ERR"}%-12s          (${e.getClass.getSimpleName})")
          Timing("PARSE_ERR")
        case Success(parsed) =>
          val cprob = toClausificationProblem(parsed)
          val hyps = cprob.hypotheses.size
          val cj = if cprob.conjecture.isDefined then "y" else "-"
          val fsize = problemSize(cprob)
          if fsize > maxSize then
            println(f"$name%-20s $hyps%4d $cj%3s  ${"SKIPPED"}%-12s  (|F|=$fsize > $maxSize)")
            return Timing("SKIPPED")
          val res = withTimeout(timeoutMs + 5000L)(solveOne(cprob, timeoutMs, maxGiven, certified, equality)) match
            case Some(Success(t)) => t
            case Some(Failure(e)) => Timing(s"ERROR(${e.getClass.getSimpleName})")
            case None             => Timing("HARD_TIMEOUT")
          println(f"$name%-20s $hyps%4d $cj%3s  ${res.category}%-12s ${res.clausifyMs}%10.1f ${res.proverMs}%10.1f ${res.checkMs}%9.1f")
          res

  /** A non-refutation ([[Bridge.Outcome]] `Saturated`/`Timeout`) thrown by the back-end to abort clausification. */
  private final class NonRefutation(val outcome: Bridge.Outcome) extends RuntimeException

  /** Run the (un)certified pipeline once, timing each phase. The prover is timed from **inside** its closure
   *  (accumulated nanos), so clausification time = total − prover even though `certifyClausal` calls the prover
   *  mid-descent (CPS). Runs on the worker thread inside [[withTimeout]]. */
  private def solveOne(cprob: Clausification.Problem, timeoutMs: Long, maxGiven: Int, certified: Boolean, equality: Boolean = true): Timing =
    val proverNanos = new java.util.concurrent.atomic.AtomicLong(0L)
    val prover: Clausification.Problem => K.SCProof = p =>
      val ps = System.nanoTime()
      try
        Clausal.proveOutcome(p, maxGiven, timeoutMs, equality) match
          case Right(proof) => proof
          case Left(other)  => throw new NonRefutation(other)
      finally proverNanos.addAndGet(System.nanoTime() - ps)
    val t0 = System.nanoTime()
    def clausifyMsSoFar: Double = (System.nanoTime() - t0 - proverNanos.get) / 1e6
    try
      val proof =
        if certified then Clausification.certifyClausal(cprob, prover)
        else UncertifiedClausification.uncertifyClausal(cprob, prover)
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
      case e: Throwable            => Timing(s"CLAUSIFY_ERR(${e.getClass.getSimpleName})", clausifyMsSoFar, proverNanos.get / 1e6)

  /** Pull hypotheses + conjecture from a parsed TPTP problem (axiom-like roles → LHS-free hypotheses). */
  private def toClausificationProblem(p: lisa.tptp.Problem): Clausification.Problem =
    val hyps = p.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if axiomLikeRoles.contains(s.role) => s.sequent
    }
    val conj = p.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if s.role == "conjecture" => s.sequent
    }
    Clausification.Problem(hyps, conj)

  /** Run `body` on a daemon thread; return its outcome, or `None` if it doesn't finish within `ms` (the
   *  worker is interrupted best-effort so the cooperatively-polling clausifier/solver can unwind). */
  private def withTimeout[T](ms: Long)(body: => T): Option[Try[T]] =
    val box = new AtomicReference[Option[Try[T]]](None)
    val th = new Thread(() => box.set(Some(Try(body))))
    th.setDaemon(true)
    th.start()
    th.join(ms)
    if th.isAlive then th.interrupt()
    box.get()

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

    def median(xs: Seq[Double]): Double = if xs.isEmpty then 0.0 else xs.sorted.apply(xs.size / 2)
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
