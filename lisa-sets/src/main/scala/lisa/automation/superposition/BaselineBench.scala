package lisa.automation.superposition

import java.io.File
import java.util.concurrent.atomic.AtomicReference
import scala.util.{Success, Failure, Using}

import lisa.utils.K
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.{Clausification, UncertifiedClausification}
import lisa.automation.clausification.Clausification.problemSize
import BenchUtil.{withTimeout, toClausificationProblem}

/**
 * A uniform, **reconstruction-free** throughput baseline across all three evaluation datasets (the clausal
 * [[Evaluation]] set, the equality-free [[FofEvaluation]] set, and the equality-bearing [[EqFofEvaluation]]
 * set), drawn with the same seeded shuffle each of those harnesses uses so the sample is identical.
 *
 * Each problem is parsed, clausified with the **non-proof-producing** clausifier
 * ([[UncertifiedClausification.clausalForm]] — the pure clause computation, no clausification proof), and then
 * refuted with [[Clausal.solveOutcome]], which runs the DISCOUNT loop to a verdict and **does not reconstruct a
 * kernel proof**. So the two timed phases are exactly clausification and prover search, with no proof machinery
 * on either side. Per problem it reports: the phase times (ms), the total, the number of **given** clauses the
 * loop processed, and the number of clauses **derived** (ever enqueued to passive). Output rows are
 * tab-separated for easy post-processing, next to E on the same sample.
 *
 * Equality inferences are configured per dataset: **off** for the two equality-free sets (`clausal`, `fof`) and
 * **on** for the equality set (`eq`) — the fair configuration for each problem class. Fingerprint indexing is on.
 *
 * Needs the `TPTP` env var pointing at the TPTP root (the directory containing `Problems/`). Run:
 * {{{
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.BaselineBench run <clausal|fof|eq> [n] [seed] [timeoutMs] [maxGiven] [maxSize]"
 *   TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.BaselineBench sample <clausal|fof|eq> [n] [seed]"
 * }}}
 * `sample` prints the seeded draw's TPTP-root-relative paths (one per line) so an external prover (E) can be run
 * on the exact same set.
 */
object BaselineBench:

  /** dataset key → list file (the same three lists the individual harnesses use). */
  private val lists: Map[String, String] = Map(
    "clausal" -> "tptp-clausal-fo-noeq-uns.txt",
    "fof" -> "tptp-fof-fo-noeq-thm.txt",
    "eq" -> "tptp-fof-fo-eq-thm.txt"
  )

  /** Equality inferences on iff the dataset is the equality-bearing one. */
  private def equalityFor(dataset: String): Boolean = dataset == "eq"

  private def allProblems(dataset: String): Vector[String] =
    val fn = lists.getOrElse(dataset, throw new IllegalArgumentException(s"unknown dataset '$dataset' (use ${lists.keys.mkString("/")})"))
    val f = BenchUtil.locateList(fn).getOrElse(throw new java.io.FileNotFoundException(s"could not find $fn"))
    Using(scala.io.Source.fromFile(f))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get

  /** The same reproducible draw each harness uses (`Random(seed).shuffle(all).take(n)`). */
  def sample(dataset: String, n: Int, seed: Long): Vector[String] =
    new scala.util.Random(seed).shuffle(allProblems(dataset)).take(n)

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
    var refuted = 0
    files.foreach { path =>
      val r = solveRow(new File(path), timeoutMs, 100000, 50000, equality = true, PrecedenceScheme.InvFrequency)
      if r.category == "REFUTED" then refuted += 1
      println(f"ROW\t${r.name}\t${r.category}\t${r.clausifyMs}%.1f\t${r.proverMs}%.1f\t${r.clausifyMs + r.proverMs}%.1f\t${r.processed}\t${r.derived}")
    }
    println(s"# REFUTED_COUNT=$refuted  (on known-satisfiable inputs, ANY refutation indicates UNSOUNDNESS)")

  private def parsePrecedence(s: String): PrecedenceScheme = s.toLowerCase match
    case "occurrence"   => PrecedenceScheme.Occurrence
    case "invfrequency" => PrecedenceScheme.InvFrequency
    case "arity"        => PrecedenceScheme.Arity
    case "unaryfirst"   => PrecedenceScheme.UnaryFirst
    case other          => throw new IllegalArgumentException(s"unknown precedence scheme '$other'")

  /** One problem's outcome + phase breakdown (all reconstruction-free). */
  private final case class Row(name: String, category: String, clausifyMs: Double, proverMs: Double, processed: Int, derived: Int)

  private def run(dataset: String, n: Int, seed: Long, timeoutMs: Long, maxGiven: Int, maxSize: Int, precedence: PrecedenceScheme): Unit =
    val tptpRoot: Option[File] = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if tptpRoot.isEmpty then { println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/)."); return }
    val eq = equalityFor(dataset)
    val picked = sample(dataset, n, seed)
    println(s"# dataset=$dataset list=${lists(dataset)} seed=$seed n=${picked.size} timeout=${timeoutMs}ms maxGiven=$maxGiven maxSize=$maxSize equality=$eq precedence=$precedence index=true (uncertified clausification, NO reconstruction)")
    println("# ROW\tproblem\tresult\tclausify_ms\tprover_ms\ttotal_ms\tgiven\tderived")
    picked.foreach { rel =>
      val r = solveRow(new File(tptpRoot.get, rel), timeoutMs, maxGiven, maxSize, eq, precedence)
      println(f"ROW\t${r.name}\t${r.category}\t${r.clausifyMs}%.1f\t${r.proverMs}%.1f\t${r.clausifyMs + r.proverMs}%.1f\t${r.processed}\t${r.derived}")
    }

  private def solveRow(f: File, timeoutMs: Long, maxGiven: Int, maxSize: Int, equality: Boolean, precedence: PrecedenceScheme): Row =
    val name = f.getName
    if !f.exists then return Row(name, "MISSING", 0, 0, 0, 0)
    (try Success(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
     catch { case e: Throwable => Failure(e) }) match
      case Failure(_) => Row(name, "PARSE_ERR", 0, 0, 0, 0)
      case Success(parsed) =>
        val cprob = toClausificationProblem(parsed)
        if problemSize(cprob) > maxSize then Row(name, "SKIPPED", 0, 0, 0, 0)
        else
          withTimeout(timeoutMs + 5000L)(measure(cprob, timeoutMs, maxGiven, equality, precedence)) match
            case Some(Success(r)) => r.copy(name = name)
            case Some(Failure(e)) => Row(name, s"ERROR(${e.getClass.getSimpleName})", 0, 0, 0, 0)
            case None             => Row(name, "HARD_TIMEOUT", 0, 0, 0, 0)

  /** Time the two phases: uncertified clausal-form computation, then reconstruction-free saturation. */
  private def measure(cprob: Clausification.Problem, timeoutMs: Long, maxGiven: Int, equality: Boolean, precedence: PrecedenceScheme): Row =
    val c0 = System.nanoTime()
    val clausal = UncertifiedClausification.clausalForm(cprob)
    val clausifyMs = (System.nanoTime() - c0) / 1e6
    val stats = new AtomicReference[Discount.LoopStats](Discount.LoopStats(0, 0, 0, 0))
    val p0 = System.nanoTime()
    val outcome: Bridge.Outcome =
      try Clausal.solveOutcome(clausal, maxGiven, timeoutMs, equality = equality, precedenceScheme = precedence, onStats = stats.set)
      catch case _: InterruptedException => Bridge.Outcome.Timeout
    val proverMs = (System.nanoTime() - p0) / 1e6
    val cat = outcome match
      case _: Bridge.Outcome.Success => "REFUTED"
      case Bridge.Outcome.Saturated  => "SATURATED"
      case Bridge.Outcome.Timeout    => "TIMEOUT"
    val s = stats.get
    Row("", cat, clausifyMs, proverMs, s.givenProcessed, s.passiveEnqueued)

