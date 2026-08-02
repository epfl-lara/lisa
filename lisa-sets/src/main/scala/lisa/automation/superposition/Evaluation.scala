package lisa.automation.superposition

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
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.Evaluation [seed] [n] [timeoutMs] [maxGiven] [subs] [gen] [unit] [sr] [cond] [equality]"
 * }}}
 * `subs`, `unit`, and `sr` each select a `both` / `fwd` / `bwd` / `none` configuration, for subsumption,
 * unit deletion, and general (multi-literal-side) subsumption resolution respectively; `cond` is `on`/`off`
 * for condensation. Defaults: `subs` and `unit` on, `sr` and `cond` off. `gen` (orthogonal) controls *where*
 * forward simplification runs: `gen` on freshly generated clauses **and** at given-selection; `nogen`
 * (default) only at given-selection. `equality` is `on`/`off` (default on): `off` skips all equality
 * inferences (superposition, equality resolution/factoring, demodulation) — this list is equality-free, so
 * `off` measures the cost of the equality machinery running inertly.
 * The solve loop honours `timeoutMs` cooperatively (checked per given clause), so a budgeted run stops
 * cleanly; a daemon-thread hard cap a few seconds later only backstops a pathological single step.
 */
object Evaluation:

  /** The generated full list (paths relative to the TPTP root, e.g. `Problems/SYN/SYN048-1.p`). */
  private val listFileName = "tptp-clausal-fo-noeq-uns.txt"

  def main(args: Array[String]): Unit =
    val (fwd, bwd) = directionMode(args.lift(4), "subsumption")
    val (fwdUD, bwdUD) = directionMode(args.lift(6), "unit-deletion")
    val (fwdSR, bwdSR) = args.lift(7) match
      case None => (false, false) // general subsumption resolution is off by default
      case some => directionMode(some, "subsumption-resolution")
    benchmark(
      seed = args.lift(0).map(_.toLong).getOrElse(0L),
      n = args.lift(1).map(_.toInt).getOrElse(100),
      timeoutMs = args.lift(2).map(_.toLong).getOrElse(15000L),
      maxGiven = args.lift(3).map(_.toInt).getOrElse(100000),
      forwardSubsumption = fwd,
      backwardSubsumption = bwd,
      forwardUnitDeletion = fwdUD,
      backwardUnitDeletion = bwdUD,
      forwardSubsumptionResolution = fwdSR,
      backwardSubsumptionResolution = bwdSR,
      condensation = onOffMode(args.lift(8), "condensation", default = false),
      forwardSimplifyAtGeneration = generationMode(args.lift(5)),
      equality = onOffMode(args.lift(9), "equality", default = true)
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
      forwardSubsumptionResolution: Boolean = false,
      backwardSubsumptionResolution: Boolean = false,
      condensation: Boolean = false,
      forwardSimplifyAtGeneration: Boolean = false,
      equality: Boolean = true): Unit =
    val tptpRoot: Option[File] = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if tptpRoot.isEmpty then
      println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/).")
      return
    BenchUtil.locateList(listFileName, Some("TPTP_CNF_LIST")) match
      case None =>
        println(s"Could not find $listFileName (looked via TPTP_CNF_LIST and relative to the working dir).")
      case Some(list) =>
        val all: Vector[String] =
          Using(scala.io.Source.fromFile(list))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get
        val sample: Vector[String] = new scala.util.Random(seed).shuffle(all).take(n)
        val cfg: String =
          s"fwdSubs=$forwardSubsumption bwdSubs=$backwardSubsumption fwdUD=$forwardUnitDeletion bwdUD=$backwardUnitDeletion " +
            s"fwdSR=$forwardSubsumptionResolution bwdSR=$backwardSubsumptionResolution cond=$condensation fwdSimplifyAtGen=$forwardSimplifyAtGeneration equality=$equality"
        println(s"list=${list.getPath} (${all.size} problems), seed=$seed, n=${sample.size}, timeout=${timeoutMs}ms, maxGiven=$maxGiven, $cfg")
        printHeader()
        report(
          sample.map(rel =>
            solveRow(
              new File(tptpRoot.get, rel), timeoutMs, maxGiven, forwardSubsumption, backwardSubsumption,
              forwardUnitDeletion, backwardUnitDeletion, forwardSubsumptionResolution, backwardSubsumptionResolution,
              condensation, forwardSimplifyAtGeneration, equality
            )
          ),
          sample.size
        )

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
      forwardSubsumptionResolution: Boolean = false,
      backwardSubsumptionResolution: Boolean = false,
      condensation: Boolean = false,
      forwardSimplifyAtGeneration: Boolean = false,
      equality: Boolean = true): (String, Long) =
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
            Bridge.solveTPTPProblem(
              problem, maxGiven, timeoutMs, forwardSubsumption, backwardSubsumption, forwardUnitDeletion,
              backwardUnitDeletion, forwardSubsumptionResolution, backwardSubsumptionResolution, condensation,
              forwardSimplifyAtGeneration, equality
            )
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


  /** First TPTP header value for `key` (e.g. `"SPC"`), read from the leading `% key : value` comments. */
  private def header(f: File, key: String): Option[String] =
    Using(scala.io.Source.fromFile(f))(
      _.getLines().find(_.matches(s"%\\s*$key\\s*:.*")).map(_.replaceFirst(s"%\\s*$key\\s*:\\s*", "").trim)
    ).toOption.flatten

  /** Number of `cnf(...)` clauses declared directly in the file (excludes `include`d axioms). */
  private def clauseCount(f: File): Int =
    Using(scala.io.Source.fromFile(f))(_.getLines().count(_.trim.startsWith("cnf("))).getOrElse(0)
