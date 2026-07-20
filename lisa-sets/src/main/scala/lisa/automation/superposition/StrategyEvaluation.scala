package lisa.automation.superposition

import java.io.File
import java.util.concurrent.atomic.AtomicReference
import scala.util.{Try, Success, Failure}

import lisa.utils.K
import lisa.tptp.{AnnotatedFormula, AnnotatedSequent}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.{Clausification, UncertifiedClausification}

/**
 * Strategy-comparison harness. Runs one or more named [[Strategy]] over the seeded FOF sample
 * ([[FofEvaluation.sample]], which honours the `TPTP_FOF_LIST` override) through the **CASC path** — uncertified
 * clausification + per-invocation SInE gate ([[SinePolicy]]) + [[Strategy.solveOutcome]] — and reports the
 * outcome breakdown (refuted / saturated / timeout / error) per strategy. No proof is built or kernel-checked;
 * we only want the search verdict, exactly what a CASC worker would produce.
 *
 * Unlike [[FofEvaluation]]/[[EqFofEvaluation]] it does **not** skip large problems (no `maxSize`): the point is
 * to see how each strategy — and its SInE filter, on the SUMO/CSR theories included via `TPTP_FOF_LIST` — copes
 * with the big problems we used to drop. Each problem runs on its own daemon thread under a hard wall-clock cap,
 * so a single blow-up (parser overflow, clausification explosion) is contained, not fatal to the run.
 *
 * {{{
 *   TPTP=/path TPTP_FOF_LIST=/path/list.txt \
 *     sbt -J-Xmx8g "lisa-sets/runMain lisa.automation.superposition.StrategyEvaluation [seed] [n] [timeoutMs] [strat1,strat2,...]"
 * }}}
 */
object StrategyEvaluation:

  def main(args: Array[String]): Unit =
    val seed      = args.lift(0).map(_.toLong).getOrElse(42L)
    val n         = args.lift(1).map(_.toInt).getOrElse(100)
    val timeoutMs = args.lift(2).map(_.toLong).getOrElse(10000L)
    val names     = args.lift(3).map(_.split(",").toList.map(_.trim)).getOrElse(List("balanced", "weight-greedy", "age-fair", "unary-redundancy"))
    val tptpRoot  = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if tptpRoot.isEmpty then { println("Set TPTP to the TPTP root (the directory containing Problems/)."); return }
    val strategies = names.flatMap(Strategy.byName)
    if strategies.size != names.size then
      println(s"unknown strategy in [${names.mkString(",")}]; available: ${Strategy.portfolio.map(_.name).mkString(", ")}")
      return
    val picked = FofEvaluation.sample(n, seed)
    val nCsr = picked.count(_.contains("/CSR/"))
    println(s"seed=$seed n=${picked.size} timeout=${timeoutMs}ms strategies=${names.mkString(",")} (NO size filter; $nCsr CSR/SUMO problems in the sample)")
    val summaries = strategies.map { strat =>
      println(s"\n===== ${strat.name} =====")
      println(f"${"PROBLEM"}%-22s ${"RESULT"}%-18s ${"ms"}%8s")
      val cats = picked.map(rel => runOne(new File(tptpRoot.get, rel), strat, timeoutMs))
      report(strat.name, cats, picked.size)
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
          val cprob = toProblem(parsed)
          // Per-invocation SInE gate — exactly the CascProver logic (self-decided, nothing shared).
          val pruned = strat.sine match
            case Some(cfg) if SinePolicy.shouldFilter(cprob, SinePolicy.Params()) => Sine.select(cprob, cfg)
            case _                                                                => cprob
          val clauses = UncertifiedClausification.clausalFormWithOrigins(pruned, orthologic = strat.orthologic)
          val goal    = clauses.iterator.zipWithIndex.collect { case ((_, o), i) if o == pruned.hypotheses.size => i }.toSet
          // Same as CascProver: add the TPTP distinct-object distinctness axioms before solving.
          val distinct = Clausal.distinctObjectAxioms(clauses.map(_._1))
          val clausal  = Clausification.Problem((clauses.map(_._1) ++ distinct).toList, None)
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

  /** Pull hypotheses + conjecture from a parsed TPTP problem (axiom-like roles → hypotheses). */
  private def toProblem(p: lisa.tptp.Problem): Clausification.Problem =
    val hyps = p.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if axiomLikeRoles.contains(s.role) => s.sequent
    }
    val conj = p.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if s.role == "conjecture" => s.sequent
    }
    Clausification.Problem(hyps, conj)

  private def report(name: String, cats: Seq[String], total: Int): String =
    def c(p: String => Boolean): Int = cats.count(p)
    val s = f"[$name] refuted=${c(_ == "REFUTED")}%3d  saturated=${c(_ == "SATURATED")}%3d  timeout=${c(_ == "TIMEOUT")}%3d  " +
      f"hard_timeout=${c(_ == "HARD_TIMEOUT")}%2d  error=${c(_.startsWith("ERROR"))}%2d  parse_err=${c(_ == "PARSE_ERR")}%3d  missing=${c(_ == "MISSING")}%2d  of $total"
    println(s); s

  /** Run `body` on a daemon thread; return its outcome, or `None` if it doesn't finish within `ms`. */
  private def withTimeout[T](ms: Long)(body: => T): Option[Try[T]] =
    val box = new AtomicReference[Option[Try[T]]](None)
    val th = new Thread(() => box.set(Some(Try(body))))
    th.setDaemon(true); th.start(); th.join(ms)
    if th.isAlive then th.interrupt()
    box.get()
