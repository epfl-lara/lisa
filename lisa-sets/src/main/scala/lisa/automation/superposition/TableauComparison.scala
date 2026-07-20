package lisa.automation.superposition

import java.io.File
import scala.util.{Success, Failure}

import lisa.utils.K
import lisa.tptp.KernelParser.{problemToKernel, problemToSequent, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.Tableau
import BenchUtil.withTimeout

/**
 * Baseline comparison harness (NOT a test -- it has a `main`): runs Lisa's existing `Tableau` tactic
 * **as is** on the *same* sample of **non-clausal** (FOF), first-order, equality-free TPTP theorems that
 * [[FofEvaluation]] uses (`tptp-fof-fo-noeq-thm.txt`, drawn with `FofEvaluation.sample`), with the same
 * seeded draw and the same wall-clock timeout — so its solved count is directly comparable to what our
 * clausify-then-refute pipeline scores via `FofEvaluation` on the identical 100 problems.
 *
 * Each problem is fed to Tableau exactly the way `lisa.tptp.TPTP_Lisa` does: parse the FOF problem and
 * build the goal `axioms ⊢ conjecture` via [[problemToSequent]], then call `Tableau.solve`. Tableau's own
 * iterative-deepening schedule would otherwise run for ~135s, so we bound it to `timeoutMs` via its
 * thread-local `setDeadline` (set **inside** the worker thread, since it is thread-local), plus a
 * daemon-thread hard cap a few seconds later -- mirroring [[FofEvaluation]].
 *
 * Needs the `TPTP` env var pointing at the TPTP root (the directory containing `Problems/`). Run:
 * {{{
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.TableauComparison [seed] [n] [timeoutMs]"
 * }}}
 * Defaults `seed=42 n=100 timeoutMs=15000`, matching [[FofEvaluation]]'s defaults so the 100 problems and
 * the budget are identical. For our prover's number on the same sample, run `FofEvaluation` with the same
 * `seed n timeoutMs`. Prints a per-problem row and a summary with Tableau's solved count.
 */
object TableauComparison:

  def main(args: Array[String]): Unit =
    run(
      seed = args.lift(0).map(_.toLong).getOrElse(42L),
      n = args.lift(1).map(_.toInt).getOrElse(100),
      timeoutMs = args.lift(2).map(_.toLong).getOrElse(15000L)
    )

  def run(seed: Long, n: Int, timeoutMs: Long): Unit =
    val tptpRoot: Option[File] = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if tptpRoot.isEmpty then
      println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/).")
      return
    val sample: Vector[String] = FofEvaluation.sample(n, seed) // the exact same 100 FOF problems FofEvaluation scores
    println(s"list=tptp-fof-fo-noeq-thm.txt (${FofEvaluation.allProblems.size} problems), seed=$seed, n=${sample.size}, timeout=${timeoutMs}ms  [Tableau, non-clausal]")
    println(f"${"PROBLEM"}%-20s ${"RESULT"}%-12s ${"ms"}%8s")
    val rows: Seq[String] = sample.map { rel =>
      val f = new File(tptpRoot.get, rel)
      val (res, ms) = solveRow(f, timeoutMs)
      println(f"${f.getName}%-20s $res%-12s $ms%8d")
      res
    }
    report(rows, sample.size)

  /** Parse one FOF problem and run Tableau on it under the same budget (kernel-checking any proof). */
  private def solveRow(f: File, timeoutMs: Long): (String, Long) =
    if !f.exists then ("MISSING", 0L)
    else
      // Catch Throwable: the recursive TPTP parser can StackOverflowError on deeply-nested FOF formulas.
      (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
       catch { case e: Throwable => Failure(e) }) match
        case Failure(_)       => ("PARSE_ERR", 0L)
        case Success(problem) =>
          val t0 = System.nanoTime()
          val outcome = withTimeout(timeoutMs + 5000L) {
            // setDeadline is thread-local, so it must run on THIS worker thread (the one calling solve).
            Tableau.setDeadline(System.currentTimeMillis() + timeoutMs)
            Tableau.solve(problemToSequent(problem)) // withTimeout wraps this in a Try
          }
          val ms = (System.nanoTime() - t0) / 1000000
          val result = outcome match
            case None                       => "HARD_TIMEOUT" // includes StackOverflowError (fatal; not caught by Try)
            case Some(Failure(_))           => "ERROR"
            case Some(Success(Some(proof))) => if K.SCProofChecker.checkSCProof(proof).isValid then "SOLVED" else "BAD_PROOF"
            case Some(Success(None))        => "UNSOLVED" // exhausted its schedule or hit the deadline
          (result, ms)

  private def report(rows: Seq[String], total: Int): Unit =
    def c(x: String): Int = rows.count(_ == x)
    println(
      s"\nTABLEAU: solved=${c("SOLVED")}  unsolved=${c("UNSOLVED")}  hard_timeout=${c("HARD_TIMEOUT")}  " +
        s"error=${c("ERROR")}  bad_proof=${c("BAD_PROOF")}  parse_err=${c("PARSE_ERR")}  of $total"
    )
    println(s"\nSOLVED: tableau=${c("SOLVED")} / $total")

