package lisa.automation.superposition
package bench

import java.io.File
import scala.util.{Success, Failure}

import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import BenchUtil.{withTimeout, toClausificationProblem}

/**
 * Runs one or more named [[Strategy]] over the same sample through the competition path (uncertified
 * clausification, the [[Sine.shouldFilter]] gate, [[Strategy.solveOutcome]]) and reports the outcome breakdown
 * per strategy. No proof is built, since only the verdict is wanted. Unlike the other harnesses it does not
 * skip large problems, which are exactly where axiom selection should help; each runs on its own thread under
 * a hard cap, so one blow-up does not end the run.
 *
 * {{{
 *   TPTP=/path TPTP_FOF_LIST=/path/list.txt \
 *     sbt -J-Xmx8g "lisa-sets/runMain lisa.automation.superposition.bench.StrategyEvaluation [seed] [n] [timeoutMs] [strat1,strat2,...]"
 * }}}
 */
object StrategyEvaluation:

  def main(args: Array[String]): Unit =
    val seed      = args.lift(0).map(_.toLong).getOrElse(42L)
    val n         = args.lift(1).map(_.toInt).getOrElse(100)
    val timeoutMs = args.lift(2).map(_.toLong).getOrElse(10000L)
    val names     = args.lift(3).map(_.split(",").toList.map(_.trim)).getOrElse(List("balanced", "weight-greedy", "age-fair", "unary-redundancy"))
    val tptpRoot  = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    val strategies = names.flatMap(Strategy.byName)
    if strategies.size != names.size then
      println(s"unknown strategy in [${names.mkString(",")}]; available: ${Strategy.portfolio.map(_.name).mkString(", ")}")
      return
    val picked = FofEvaluation.sample(n, seed)
    val nCsr = picked.count(_.contains("/CSR/"))
    println(s"seed=$seed n=${picked.size} timeout=${timeoutMs}ms strategies=${names.mkString(",")} (NO size filter; $nCsr CSR/SUMO problems in the sample)")
    // Reset per strategy: a worker abandoned under one strategy hurts the strategies that follow, which is
    // exactly the comparison this harness exists to make, so each block reports its own contamination.
    val summaries = strategies.map { strat =>
      println(s"\n===== ${strat.name} =====")
      println(f"${"PROBLEM"}%-22s ${"RESULT"}%-18s ${"ms"}%8s")
      BenchUtil.resetAbandoned()
      val cats = picked.map(rel => runOne(new File(tptpRoot.get, rel), strat, timeoutMs))
      val line = report(strat.name, cats, picked.size)
      val warning = BenchUtil.contaminationWarning
      if warning.nonEmpty then println(warning)
      if warning.isEmpty then line else s"$line  [CONTAMINATED: ${BenchUtil.abandonedWorkers} abandoned worker(s)]"
    }
    println("\n=== summary ===")
    summaries.foreach(println)

  private def runOne(f: File, strat: Strategy, timeoutMs: Long): String =
    val name = f.getName
    if !f.exists then { println(f"$name%-22s ${"MISSING"}%-18s"); return "MISSING" }
    val t0 = System.nanoTime()
    val cat = withTimeout(timeoutMs + 10000L) {
      (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
       catch { case e: Throwable => Failure(e) }) match
        case Failure(_) => "PARSE_ERR"
        case Success(parsed) =>
          val cprob = toClausificationProblem(parsed)
          // Per-invocation SInE gate, exactly the CascProver logic (self-decided, nothing shared).
          val pruned = strat.sine match
            case Some(cfg) if Sine.shouldFilter(cprob, Sine.Params()) => Sine.select(cprob, cfg)
            case _                                                                => cprob
          // Uncertified clausify + distinct-object axioms + goal-clause indices, shared with CascProver.
          val (_, clausal, goal) = Clausal.cascSetup(pruned, orthologic = strat.orthologic)
          strat.solveOutcome(clausal, maxMillis = timeoutMs, goal = goal) match
            case _: Bridge.Outcome.Success => "REFUTED"
            case Bridge.Outcome.Saturated  => "SATURATED"
            case Bridge.Outcome.Timeout    => "TIMEOUT"
    } match
      case Some(Success(c)) => c
      case Some(Failure(e)) => s"ERROR(${e.getClass.getSimpleName})"
      case None             => "HARD_TIMEOUT" // hard wall-clock cap hit, or a fatal error (OOM) killed the worker
    println(f"$name%-22s $cat%-18s ${(System.nanoTime() - t0) / 1e6}%8.0f")
    cat

  private def report(name: String, cats: Seq[String], total: Int): String =
    def c(p: String => Boolean): Int = cats.count(p)
    val s = f"[$name] refuted=${c(_ == "REFUTED")}%3d  saturated=${c(_ == "SATURATED")}%3d  timeout=${c(_ == "TIMEOUT")}%3d  " +
      f"hard_timeout=${c(_ == "HARD_TIMEOUT")}%2d  error=${c(_.startsWith("ERROR"))}%2d  parse_err=${c(_ == "PARSE_ERR")}%3d  missing=${c(_ == "MISSING")}%2d  of $total"
    println(s); s

