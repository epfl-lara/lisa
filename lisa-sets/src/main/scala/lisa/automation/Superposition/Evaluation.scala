package lisa.automation.superposition

import java.io.File
import scala.util.{Try, Success, Failure, Using}

import lisa.tptp.Problem
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}

/**
 * Performance-evaluation harness for the Phase-1 resolution prover (NOT a test — it has a `main`).
 *
 * It runs [[Bridge.solveProblem]] over a curated list of TPTP clausal problems and prints a timing
 * table. The problems are all **no-equality, unsatisfiable** (the prover has no paramodulation yet, so
 * equality problems would just time out uniformly), but otherwise varied — they span EPR (decidable)
 * vs RFO (real first-order, semi-decidable) and Horn vs non-Horn, across clause counts — so the table
 * shows a real performance gradient rather than the trivially-decidable EPR-Horn fragment.
 *
 * Run (the `TPTP` env var must point at the TPTP root, i.e. the dir containing `Problems/`):
 * {{{
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.Evaluation [timeoutMs] [maxGiven]"
 * }}}
 * Each solve runs on a daemon thread with a wall-clock timeout; a timed-out solve is abandoned (it
 * keeps running in the background until it hits `maxGiven`, so keep `maxGiven` modest).
 */
object Evaluation:

  /** Problem paths relative to `$TPTP/Problems`, grouped by fragment and ascending size. */
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
    val timeoutMs: Long = args.lift(0).map(_.toLong).getOrElse(10000L)
    val maxGiven: Int = args.lift(1).map(_.toInt).getOrElse(100000)
    val problemsDir: Option[File] = sys.env.get("TPTP").map(t => new File(t, "Problems")).filter(_.isDirectory)
    if problemsDir.isEmpty then
      println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/).")
      return

    println(s"timeout = ${timeoutMs}ms, maxGiven = $maxGiven")
    println(f"${"PROBLEM"}%-18s ${"SPC"}%-22s ${"CLS"}%4s  ${"RESULT"}%-9s ${"ms"}%8s")
    var refuted, unsolved, timeouts, errors = 0
    var refutedMs = 0L

    for rel <- problems do
      val f = new File(problemsDir.get, rel)
      val name = f.getName
      if !f.exists then println(f"$name%-18s ${"-- file not found --"}")
      else
        val spc = header(f, "SPC").getOrElse("?")
        val cls = clauseCount(f)
        Try(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))) match
          case Failure(e) =>
            errors += 1
            println(f"$name%-18s $spc%-22s $cls%4d  ${"PARSE_ERR"}%-9s         ($e)")
          case Success(problem) =>
            val t0 = System.nanoTime()
            val outcome = withTimeout(timeoutMs)(Bridge.solveProblem(problem, maxGiven))
            val ms = (System.nanoTime() - t0) / 1000000
            val result = outcome match
              case None => timeouts += 1; "TIMEOUT"
              case Some(Failure(e)) => errors += 1; s"ERROR($e)"
              case Some(Success(true)) => refuted += 1; refutedMs += ms; "REFUTED"
              case Some(Success(false)) => unsolved += 1; "UNSOLVED"
            println(f"$name%-18s $spc%-22s $cls%4d  $result%-9s $ms%8d")

    println(s"\nrefuted=$refuted  unsolved=$unsolved  timeout=$timeouts  error=$errors  (of ${problems.size})")
    if refuted > 0 then println(s"total refute time = ${refutedMs}ms, avg = ${refutedMs / refuted}ms")

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
