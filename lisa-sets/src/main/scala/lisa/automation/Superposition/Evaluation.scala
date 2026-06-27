package lisa.automation.superposition

import java.io.File
import scala.util.{Try, Success, Failure, Using}

import lisa.utils.K
import lisa.tptp.Problem
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}

/**
 * Performance-evaluation harness for the Phase-1 resolution prover (NOT a test -- it has a `main`).
 *
 * Two modes:
 *   - [[benchmark]] (the default): take a seeded **random sample** of `n` problems from the generated
 *     list of clausal, first-order, equality-free, **unsatisfiable** TPTP problems
 *     (`tptp-clausal-fo-noeq-uns.txt`) and try to solve each within a wall-clock budget. Reproducible:
 *     the same seed picks the same sample. Since every problem is unsatisfiable, `REFUTED` vs `TIMEOUT`
 *     is the throughput axis, and a `SATURATED` (claiming satisfiable) would itself be a bug.
 *   - [[runCurated]]: the older hand-picked list in [[problems]] (a quick fixed set, no equality, varied
 *     across the EPR/RFO and Horn/non-Horn fragments).
 *
 * Both need the `TPTP` env var pointing at the TPTP root (the directory containing `Problems/`). Run:
 * {{{
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.Evaluation [seed] [n] [timeoutMs] [maxGiven] [subs] [gen] [unit]"
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.Evaluation curated [timeoutMs] [maxGiven]"
 * }}}
 * `subs` and `unit` each select a `both` (default) / `fwd` / `bwd` / `none` configuration, for subsumption
 * and unit deletion respectively. `gen` (orthogonal) controls *where* forward simplification runs: `gen`
 * on freshly generated clauses **and** at given-selection; `nogen` (default) only at given-selection.
 * The solve loop honours `timeoutMs` cooperatively (checked per given clause), so a budgeted run stops
 * cleanly; a daemon-thread hard cap a few seconds later only backstops a pathological single step.
 */
object Evaluation:

  /** The generated full list (paths relative to the TPTP root, e.g. `Problems/SYN/SYN048-1.p`). */
  private val listFileName = "tptp-clausal-fo-noeq-uns.txt"

  /** Hand-picked no-equality clausal problems (paths relative to `$TPTP/Problems`), for [[runCurated]]. */
  val problems: List[String] = List(
    // EPR, non-Horn (decidable, but harder than Horn)
    "SYN/SYN051-1.p", "SYN/SYN054-1.p", "SYN/SYN009-1.p", "SYN/SYN009-3.p",
    "SYN/SYN099-1.003.p", "SYN/SYN869-1.p", "SYN/SYN876-1.p", "SYN/SYN436-1.p",
    // RFO (real first-order), Horn
    "SYN/SYN035-1.p", "SYN/SYN050-1.p", "SYN/SYN065-1.p", "SYN/SYN312-1.p",
    "SYN/SYN555-1.p", "SYN/SYN566-1.p", "SYN/SYN577-1.p", "SYN/SYN601-1.p",
    "SYN/SYN651-1.p", "SYN/SYN688-1.p", "SYN/SYN711-1.p",
    // RFO, non-Horn (the hardest no-equality fragment)
    "SYN/SYN006-1.p", "SYN/SYN069-1.p", "SYN/SYN082-1.p", "SYN/SYN328-1.p",
    "SYN/SYN567-1.p", "SYN/SYN585-1.p", "SYN/SYN604-1.p", "SYN/SYN656-1.p",
    "SYN/SYN660-1.p", "SYN/SYN686-1.p", "SYN/SYN692-1.p"
  )

  def main(args: Array[String]): Unit =
    args.headOption match
      case Some("curated") =>
        runCurated(args.lift(1).map(_.toLong).getOrElse(10000L), args.lift(2).map(_.toInt).getOrElse(100000))
      case Some("verify") =>
        verifyProblem(args.lift(1).getOrElse(""), args.lift(2).map(_.toInt).getOrElse(100000), args.lift(3).map(_.toLong).getOrElse(10000L))
      case _ =>
        val (fwd, bwd) = subsumptionMode(args.lift(4))
        val (fwdUD, bwdUD) = directionMode(args.lift(6), "unit-deletion")
        benchmark(
          seed = args.lift(0).map(_.toLong).getOrElse(0L),
          n = args.lift(1).map(_.toInt).getOrElse(100),
          timeoutMs = args.lift(2).map(_.toLong).getOrElse(15000L),
          maxGiven = args.lift(3).map(_.toInt).getOrElse(100000),
          forwardSubsumption = fwd,
          backwardSubsumption = bwd,
          forwardUnitDeletion = fwdUD,
          backwardUnitDeletion = bwdUD,
          forwardSimplifyAtGeneration = generationMode(args.lift(5))
        )

  /** Parse the optional subsumption-mode token into (forward, backward) flags. Default: both on. */
  private def subsumptionMode(arg: Option[String]): (Boolean, Boolean) = directionMode(arg, "subsumption")

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
   * and run through the kernel checker** (reusing the solve — no re-proving), so a `bad_proof` in the
   * summary flags a soundness/reconstruction bug. Prints a per-problem row and a summary. A larger `n`
   * than the list size just runs the whole list.
   */
  def benchmark(
      seed: Long,
      n: Int = 100,
      timeoutMs: Long = 15000L,
      maxGiven: Int = 100000,
      forwardSubsumption: Boolean = true,
      backwardSubsumption: Boolean = true,
      forwardUnitDeletion: Boolean = true,
      backwardUnitDeletion: Boolean = true,
      forwardSimplifyAtGeneration: Boolean = false): Unit =
    val tptpRoot: Option[File] = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if tptpRoot.isEmpty then
      println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/).")
      return
    locateListFile() match
      case None =>
        println(s"Could not find $listFileName (looked via TPTP_CNF_LIST and relative to the working dir).")
      case Some(list) =>
        val all: Vector[String] =
          Using(scala.io.Source.fromFile(list))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get
        val sample: Vector[String] = new scala.util.Random(seed).shuffle(all).take(n)
        val cfg: String =
          s"fwdSubs=$forwardSubsumption bwdSubs=$backwardSubsumption fwdUD=$forwardUnitDeletion bwdUD=$backwardUnitDeletion fwdSimplifyAtGen=$forwardSimplifyAtGeneration"
        println(s"list=${list.getPath} (${all.size} problems), seed=$seed, n=${sample.size}, timeout=${timeoutMs}ms, maxGiven=$maxGiven, $cfg")
        printHeader()
        report(
          sample.map(rel =>
            solveRow(new File(tptpRoot.get, rel), timeoutMs, maxGiven, forwardSubsumption, backwardSubsumption, forwardUnitDeletion, backwardUnitDeletion, forwardSimplifyAtGeneration)
          ),
          sample.size
        )

  /** Run the fixed curated list ([[problems]], paths relative to `$TPTP/Problems`). */
  def runCurated(timeoutMs: Long = 10000L, maxGiven: Int = 100000): Unit =
    val problemsDir: Option[File] = sys.env.get("TPTP").map(t => new File(t, "Problems")).filter(_.isDirectory)
    if problemsDir.isEmpty then
      println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/).")
      return
    println(s"curated set (${problems.size} problems), timeout=${timeoutMs}ms, maxGiven=$maxGiven")
    printHeader()
    report(problems.map(rel => solveRow(new File(problemsDir.get, rel), timeoutMs, maxGiven)), problems.size)

  /**
   * Solve one problem (path relative to the TPTP root, e.g. `Problems/GRP/GRP128-4.004.p`) within
   * `maxGiven`/`maxMillis`, and -- only if it claims a refutation -- run the reconstructed proof through
   * the kernel checker. A claimed refutation of a `Satisfiable` problem is a soundness bug; the kernel
   * check then says whether the internal clause set is really contradictory (conversion bug) or the
   * core derivation is bogus (its proof won't conclude the empty sequent).
   */
  def verifyProblem(rel: String, maxGiven: Int = 100000, maxMillis: Long = 10000L): Unit =
    val tptpRoot: Option[File] = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if tptpRoot.isEmpty then { println("Set the TPTP environment variable to the TPTP root."); return }
    val f = new File(tptpRoot.get, rel)
    if !f.exists then { println(s"not found: ${f.getPath}"); return }
    val problem = problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))
    Bridge.solveTPTPProblem(problem, maxGiven, maxMillis) match
      case Bridge.Outcome.Saturated =>
        println(s"$rel: SATURATED -- no refutation exists (the clause set is satisfiable)")
      case Bridge.Outcome.Timeout =>
        println(s"$rel: TIMEOUT -- no refutation within budget (maxGiven=$maxGiven / ${maxMillis}ms)")
      case s: Bridge.Outcome.Success =>
        val p = s.reconstructKernelProof
        val r = K.SCProofChecker.checkSCProof(p)
        println(s"$rel: REFUTED -- imports=${p.imports.size}, steps=${p.steps.size}")
        println(s"  conclusion   = ${p.conclusion}")
        println(s"  kernel valid = ${r.isValid}, conclusion empty = ${p.conclusion == K.Sequent(Set.empty, Set.empty)}")
        if !r.isValid then println(s"  checker says: $r")

  private def printHeader(): Unit =
    println(f"${"PROBLEM"}%-20s ${"SPC"}%-22s ${"CLS"}%4s  ${"RESULT"}%-12s ${"ms"}%8s")

  /** Parse + solve one problem file, kernel-check any refutation, print its table row, and return its
   *  result category and (solve-only) elapsed ms. */
  private def solveRow(
      f: File,
      timeoutMs: Long,
      maxGiven: Int,
      forwardSubsumption: Boolean = true,
      backwardSubsumption: Boolean = true,
      forwardUnitDeletion: Boolean = true,
      backwardUnitDeletion: Boolean = true,
      forwardSimplifyAtGeneration: Boolean = false): (String, Long) =
    val name = f.getName
    if !f.exists then
      println(f"$name%-20s ${"-- file not found --"}")
      ("MISSING", 0L)
    else
      val spc = header(f, "SPC").getOrElse("?")
      val cls = clauseCount(f)
      Try(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))) match
        case Failure(e) =>
          println(f"$name%-20s $spc%-22s $cls%4d  ${"PARSE_ERR"}%-12s         ($e)")
          ("PARSE_ERR", 0L)
        case Success(problem) =>
          val t0 = System.nanoTime()
          // cooperative time budget inside the loop; a daemon hard cap a few seconds later backstops a
          // pathological single step that overshoots between time checks.
          val outcome = withTimeout(timeoutMs + 5000L)(
            Bridge.solveTPTPProblem(problem, maxGiven, timeoutMs, forwardSubsumption, backwardSubsumption, forwardUnitDeletion, backwardUnitDeletion, forwardSimplifyAtGeneration)
          )
          val ms = (System.nanoTime() - t0) / 1000000
          val (result, detail) = outcome match
            case None                                      => ("HARD_TIMEOUT", "")
            case Some(Failure(e))                          => ("ERROR", s"  ($e)")
            case Some(Success(Bridge.Outcome.Saturated))   => ("SATURATED", "")
            case Some(Success(Bridge.Outcome.Timeout))     => ("TIMEOUT", "")
            case Some(Success(s: Bridge.Outcome.Success))  => checkRefutation(s)
          println(f"$name%-20s $spc%-22s $cls%4d  $result%-12s $ms%8d$detail")
          (result, ms)

  /**
   * Reconstruct a refutation's kernel proof and check it. `REFUTED` iff the proof is kernel-valid and
   * concludes the empty sequent `⊢`; otherwise `BAD_PROOF` (a soundness or reconstruction bug — e.g. a
   * "refutation" whose proof doesn't actually conclude `⊢`, as the `e_1`-collapse bug used to produce).
   * Reconstruction reuses the solve's bank/inputs (no re-proving). Returns `(category, detail)`.
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
    if refuted > 0 then println(s"refute time: total=${refutedMs}ms  avg=${refutedMs / refuted}ms")

  /** Locate the generated problem list: `TPTP_CNF_LIST`, else source-relative candidates / the cwd. */
  private def locateListFile(): Option[File] =
    val candidates: List[File] =
      sys.env.get("TPTP_CNF_LIST").map(new File(_)).toList :::
        List(
          s"lisa-sets/src/main/scala/lisa/automation/superposition/$listFileName",
          s"src/main/scala/lisa/automation/superposition/$listFileName",
          listFileName
        ).map(new File(_))
    candidates.find(_.isFile)

  /** Run `body` on a daemon thread, returning its outcome, or `None` if it does not finish within `ms`. */
  private def withTimeout[T](ms: Long)(body: => T): Option[Try[T]] =
    val box = new java.util.concurrent.atomic.AtomicReference[Option[Try[T]]](None)
    val th = new Thread(() => box.set(Some(Try(body))))
    th.setDaemon(true)
    th.start()
    th.join(ms)
    box.get()

  /** First TPTP header value for `key` (e.g. `"SPC"`), read from the leading `% key : value` comments. */
  private def header(f: File, key: String): Option[String] =
    Using(scala.io.Source.fromFile(f))(
      _.getLines().find(_.matches(s"%\\s*$key\\s*:.*")).map(_.replaceFirst(s"%\\s*$key\\s*:\\s*", "").trim)
    ).toOption.flatten

  /** Number of `cnf(...)` clauses declared directly in the file (excludes `include`d axioms). */
  private def clauseCount(f: File): Int =
    Using(scala.io.Source.fromFile(f))(_.getLines().count(_.trim.startsWith("cnf("))).getOrElse(0)
