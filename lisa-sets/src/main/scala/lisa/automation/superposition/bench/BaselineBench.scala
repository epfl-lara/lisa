package lisa.automation.superposition
package bench

import java.io.File
import java.util.concurrent.atomic.AtomicReference
import scala.util.{Success, Failure, Using}

import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.UncertifiedClausifier
import lisa.automation.Problem
import BenchUtil.withTimeout
import lisa.automation.superposition.ordering.*

/**
 * Throughput across all three datasets with no proof built on either side, so the two timed phases are exactly
 * clausification and search. Rows are tab-separated, for comparison against another prover on the same sample.
 * Equality inferences are on for the equality dataset and off for the other two, the fair setting for each.
 * Requires `TPTP` to point at the problem library.
 * {{{
 *   TPTP=/path sbt "lisa-sets/runMain lisa.automation.superposition.bench.BaselineBench run <clausal|fof|eq> [n] [seed] [timeoutMs] [maxGiven] [maxSize]"
 *   TPTP=/path sbt "lisa-sets/runMain lisa.automation.superposition.bench.BaselineBench sample <clausal|fof|eq> [n] [seed]"
 * }}}
 * `sample` prints the drawn paths, so that another prover can be run on the same set.
 */
object BaselineBench:

  /** dataset key → list file (the same three lists the individual harnesses use). */
  private val lists: Map[String, String] = Map(
    "clausal" -> "tptp-clausal-fo-noeq-uns.txt",
    "fof" -> "tptp-fof-fo-noeq-thm.txt",
    "eq" -> "tptp-fof-fo-eq-thm.txt"
  )

  private def problemsOf(dataset: String): ProblemList =
    val fn = lists.getOrElse(dataset, throw new IllegalArgumentException(s"unknown dataset '$dataset' (use ${lists.keys.mkString("/")})"))
    new ProblemList(fn)

  /** The same draw the other harnesses use, so a seed names the same problems here as there. */
  def sample(dataset: String, n: Int, seed: Long): Vector[String] = problemsOf(dataset).sample(n, seed)

  def main(args: Array[String]): Unit =
    args.headOption match
      case Some("sample") =>
        sample(args(1), args.lift(2).map(_.toInt).getOrElse(100), args.lift(3).map(_.toLong).getOrElse(42L)).foreach(println)
      case Some("run") =>
        run(
          dataset = args(1),
          n = args.lift(2).map(_.toInt).getOrElse(100),
          seed = args.lift(3).map(_.toLong).getOrElse(42L),
          timeoutMs = args.lift(4).map(_.toLong).getOrElse(15000L),
          maxGiven = args.lift(5).map(_.toInt).getOrElse(100000),
          maxSize = args.lift(6).map(_.toInt).getOrElse(50000),
          precedence = args.lift(7).map(parsePrecedence).getOrElse(PrecedenceScheme.InvFrequency)
        )
      case Some("runlist") =>
        // Soundness probe: run each problem in a file of (absolute) paths and flag any REFUTED. On a set of
        // KNOWN-SATISFIABLE problems, a REFUTED verdict means our clausification/prover is UNSOUND.
        runList(args(1), args.lift(2).map(_.toLong).getOrElse(10000L))
      case _ =>
        println("usage: BaselineBench sample <clausal|fof|eq> [n] [seed]")
        println("       BaselineBench run    <clausal|fof|eq> [n] [seed] [timeoutMs] [maxGiven] [maxSize] [precedence]")
        println("       BaselineBench runlist <pathListFile> [timeoutMs]   (soundness probe; flags any REFUTED)")
        println("       precedence ∈ {occurrence, invfrequency, arity, unaryfirst} (default invfrequency)")

  private def runList(listPath: String, timeoutMs: Long): Unit =
    val files = Using(scala.io.Source.fromFile(listPath))(_.getLines().map(_.trim).filter(_.nonEmpty).toList).get
    println(s"# runlist n=${files.size} timeout=${timeoutMs}ms equality=true precedence=InvFrequency (soundness probe)")
    println("# ROW\tproblem\tresult\tclausify_ms\tprover_ms\ttotal_ms\tgiven\tderived")
    BenchUtil.resetAbandoned()
    val rows = files.map { path =>
      val r = solveRow(new File(path), timeoutMs, 100000, 50000, equality = true, PrecedenceScheme.InvFrequency)
      printRow(r)
      r
    }
    println(s"# REFUTED_COUNT=${rows.count(_.category == "REFUTED")}  (on known-satisfiable inputs, ANY refutation indicates UNSOUNDNESS)")
    reportContamination()

  private def parsePrecedence(s: String): PrecedenceScheme = s.toLowerCase match
    case "occurrence"   => PrecedenceScheme.Occurrence
    case "invfrequency" => PrecedenceScheme.InvFrequency
    case "arity"        => PrecedenceScheme.Arity
    case "unaryfirst"   => PrecedenceScheme.UnaryFirst
    case other          => throw new IllegalArgumentException(s"unknown precedence scheme '$other'")

  /** One problem's outcome + phase breakdown (all reconstruction-free). */
  private final case class Row(name: String, category: String, clausifyMs: Double, proverMs: Double, processed: Int, derived: Int)

  /** One TSV row. Plain `toString` on the times, rounded by hand, rather than `%.1f`: the `f` interpolator
    * formats in the default locale, writing `12,3` where whatever reads this TSV expects `12.3`. */
  private def printRow(r: Row): Unit =
    def ms(x: Double): String = (math.rint(x * 10.0) / 10.0).toString
    println(Seq(r.name, r.category, ms(r.clausifyMs), ms(r.proverMs), ms(r.clausifyMs + r.proverMs),
      r.processed.toString, r.derived.toString).mkString("ROW\t", "\t", ""))

  private def run(dataset: String, n: Int, seed: Long, timeoutMs: Long, maxGiven: Int, maxSize: Int, precedence: PrecedenceScheme): Unit =
    val tptpRoot: Option[File] = BenchUtil.tptpRootOrExplain()
    if tptpRoot.isEmpty then return
    val eq = dataset == "eq" // equality inferences on only for the dataset that has equality
    val picked = sample(dataset, n, seed)
    println(s"# dataset=$dataset list=${lists(dataset)} seed=$seed n=${picked.size} timeout=${timeoutMs}ms maxGiven=$maxGiven maxSize=$maxSize equality=$eq precedence=$precedence (uncertified clausification, NO reconstruction)")
    println("# ROW\tproblem\tresult\tclausify_ms\tprover_ms\ttotal_ms\tgiven\tderived")
    BenchUtil.resetAbandoned()
    picked.foreach(rel => printRow(solveRow(new File(tptpRoot.get, rel), timeoutMs, maxGiven, maxSize, eq, precedence)))
    reportContamination()

  /** Emit the contamination warning as a `#` comment, so it survives the TSV being piped into a spreadsheet
    * or a plotting script rather than being lost with the rest of the console output. */
  private def reportContamination(): Unit =
    val warning = BenchUtil.contaminationWarning
    if warning.nonEmpty then
      println(s"# CONTAMINATED=${BenchUtil.abandonedWorkers}")
      warning.linesIterator.foreach(l => println(s"# $l"))

  private def solveRow(f: File, timeoutMs: Long, maxGiven: Int, maxSize: Int, equality: Boolean, precedence: PrecedenceScheme): Row =
    val name = f.getName
    if !f.exists then return Row(name, "MISSING", 0, 0, 0, 0)
    (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
     catch { case e: Throwable => Failure(e) }) match
      case Failure(_) => Row(name, "PARSE_ERR", 0, 0, 0, 0)
      case Success(parsed) =>
        val cprob = Prover.fromTptp(parsed)
        if cprob.size > maxSize then Row(name, "SKIPPED", 0, 0, 0, 0)
        else
          withTimeout(timeoutMs + 5000L)(measure(cprob, timeoutMs, maxGiven, equality, precedence)) match
            case Some(Success(r)) => r.copy(name = name)
            case Some(Failure(e)) => Row(name, s"ERROR(${e.getClass.getSimpleName})", 0, 0, 0, 0)
            case None             => Row(name, "HARD_TIMEOUT", 0, 0, 0, 0)

  /** Time the two phases: uncertified clausal-form computation, then reconstruction-free saturation. */
  private def measure(cprob: Problem, timeoutMs: Long, maxGiven: Int, equality: Boolean, precedence: PrecedenceScheme): Row =
    val c0 = System.nanoTime()
    val clausal = UncertifiedClausifier.clausalForm(cprob)
    val clausifyMs = (System.nanoTime() - c0) / 1e6
    val stats = new AtomicReference[Discount.LoopStats](Discount.LoopStats(0, 0, 0, 0))
    val p0 = System.nanoTime()
    val outcome: Clausal.Outcome =
      try Clausal.solve(clausal, SearchOptions(equality = equality, precedenceScheme = precedence,
        maxGiven = maxGiven, maxMillis = timeoutMs, onStats = stats.set))
      catch case _: InterruptedException => Clausal.Outcome.Timeout
    val proverMs = (System.nanoTime() - p0) / 1e6
    val cat = outcome match
      case _: Clausal.Outcome.Success => "REFUTED"
      case Clausal.Outcome.Saturated  => "SATURATED"
      case Clausal.Outcome.Timeout    => "TIMEOUT"
    val s = stats.get
    Row("", cat, clausifyMs, proverMs, s.givenProcessed, s.passiveEnqueued)

