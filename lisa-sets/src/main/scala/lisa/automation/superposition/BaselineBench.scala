package lisa.automation.superposition

import java.io.File
import java.util.concurrent.atomic.AtomicReference
import scala.util.{Try, Success, Failure, Using}

import lisa.utils.K
import lisa.tptp.{AnnotatedFormula, AnnotatedSequent}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.{Clausification, UncertifiedClausification}
import lisa.automation.clausification.Clausification.problemSize

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

  private def locate(listFileName: String): Option[File] =
    List(
      s"lisa-sets/src/main/scala/lisa/automation/superposition/$listFileName",
      s"src/main/scala/lisa/automation/superposition/$listFileName",
      listFileName
    ).map(new File(_)).find(_.isFile)

  private def allProblems(dataset: String): Vector[String] =
    val fn = lists.getOrElse(dataset, throw new IllegalArgumentException(s"unknown dataset '$dataset' (use ${lists.keys.mkString("/")})"))
    val f = locate(fn).getOrElse(throw new java.io.FileNotFoundException(s"could not find $fn"))
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
      case Some("diag") =>
        // Localise an unsoundness: run the SAME prover on (a) the fast/uncertified clauses and (b) the certified
        // clauses of one problem. fast=REFUTED & cert=SATURATED ⇒ FastClausify bug; both REFUTED ⇒ prover/loading.
        diag(args(1), args.lift(2).map(_.toLong).getOrElse(10000L))
      case _ =>
        println("usage: BaselineBench sample <clausal|fof|eq> [n] [seed]")
        println("       BaselineBench run    <clausal|fof|eq> [n] [seed] [timeoutMs] [maxGiven] [maxSize] [precedence]")
        println("       BaselineBench runlist <pathListFile> [timeoutMs]   (soundness probe; flags any REFUTED)")
        println("       precedence ∈ {occurrence, invfrequency, arity, unaryfirst} (default invfrequency)")

  private def diag(path: String, timeoutMs: Long): Unit =
    val parsed = problemToKernel(new File(path))(using (strictMapAtom, strictMapTerm, strictMapVariable))
    val cprob = toClausificationProblem(parsed)
    def outcomeOf(p: Clausification.Problem, eq: Boolean): String =
      withTimeout(timeoutMs + 5000L)(Clausal.solveOutcome(p, maxMillis = timeoutMs, equality = eq)) match
        case Some(Success(o)) => o match { case _: Bridge.Outcome.Success => "REFUTED"; case Bridge.Outcome.Saturated => "SATURATED"; case _ => "TIMEOUT" }
        case Some(Failure(e)) => s"ERROR(${e.getClass.getSimpleName})"
        case None             => "HARD_TIMEOUT"
    // (a) fast / uncertified clauses
    val fast = UncertifiedClausification.clausalForm(cprob)
    println(s"# fast clauses: ${fast.hypotheses.size}")
    fast.hypotheses.zipWithIndex.foreach { case (s, i) => println(s"# FASTCL[$i] $s") }
    println(s"FAST(eq=on)\t${outcomeOf(fast, true)}")
    println(s"FAST(eq=off)\t${outcomeOf(fast, false)}")
    // Reconstruct the fast-clause refutation and kernel-check it. VALID ⇒ clauses genuinely unsat (clausifier bug);
    // INVALID ⇒ the prover took an unsound step (reconstruction exposes it).
    withTimeout(timeoutMs + 5000L)(Clausal.proveOutcome(Clausification.Problem(fast.hypotheses, None), maxMillis = timeoutMs)) match
      case Some(Success(Right(proof))) =>
        val check = K.SCProofChecker.checkSCProof(proof)
        println(s"# RECONSTRUCT: kernel valid=${check.isValid}  conclusion=${proof.conclusion}")
        if !check.isValid then println(s"# KERNEL JUDGEMENT: $check")
      case Some(Success(Left(o))) => println(s"# RECONSTRUCT: prover did not refute ($o)")
      case Some(Failure(e))       => println(s"# RECONSTRUCT threw: ${e.getClass.getSimpleName}: ${e.getMessage}")
      case None                   => println("# RECONSTRUCT: hard timeout")
    // Minimal unsat core: greedily drop clauses while the remainder still refutes (eq on). The survivors reveal
    // the offending (non-consequence) clause.
    def refutes(cs: IndexedSeq[K.Sequent]): Boolean =
      withTimeout(timeoutMs + 5000L)(Clausal.solveOutcome(Clausification.Problem(cs.toSeq, None), maxMillis = timeoutMs, equality = true)) match
        case Some(Success(o)) => o.refuted
        case _                => false
    var core = fast.hypotheses.toIndexedSeq
    var i = 0
    while i < core.size do
      val without = core.patch(i, Nil, 1)
      if refutes(without) then core = without else i += 1
    println(s"# MINIMAL UNSAT CORE: ${core.size} clauses")
    core.zipWithIndex.foreach { case (s, k) => println(s"# CORE[$k] $s") }
    // (b) certified clauses: capture what certifyClausal feeds its prover (return a Sorry so it completes)
    var captured: Clausification.Problem = null
    try Clausification.certifyClausal(cprob, p => { captured = p; K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), p.imports) })
    catch { case e: Throwable => println(s"# certifyClausal threw: ${e.getClass.getSimpleName}: ${e.getMessage}") }
    if captured != null then
      println(s"# certified clauses: ${captured.imports.size}")
      println(s"CERT(eq=on)\t${outcomeOf(Clausification.Problem(captured.imports.toSeq, None), true)}")

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

  /** Run `body` on a daemon thread; return its outcome, or `None` if it doesn't finish within `ms`. */
  private def withTimeout[T](ms: Long)(body: => T): Option[Try[T]] =
    val box = new AtomicReference[Option[Try[T]]](None)
    val th = new Thread(() => box.set(Some(Try(body))))
    th.setDaemon(true)
    th.start()
    th.join(ms)
    if th.isAlive then th.interrupt()
    box.get()
