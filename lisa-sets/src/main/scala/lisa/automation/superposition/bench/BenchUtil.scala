package lisa.automation.superposition
package bench

import java.io.File
import java.util.concurrent.atomic.AtomicReference
import scala.util.{Try, Using}

import lisa.utils.K
import lisa.tptp.{Problem, AnnotatedFormula, AnnotatedSequent}
import lisa.tptp.KernelParser.axiomLikeRoles
import lisa.automation.clausification.Clausification

/**
 * A generated problem list (paths relative to the TPTP root) plus the seeded sampling every harness draws
 * from it. One class rather than a copy per harness because the draw has to be *identical* across them:
 * benchmark numbers are only comparable when they name the same problems.
 *
 * The list ships as a **classpath resource** under `/lisa/automation/superposition/`, so it is found the same
 * way however the harness is launched: `sbt runMain`, a forked child JVM (whose working directory is not the
 * repo root), or a packaged jar. Hence the `.txt` lists living under `src/main/resources`, not beside the
 * sources: a source-relative lookup only works from the repo root, and fails silently anywhere else.
 *
 * @param listFileName the generated list, e.g. `tptp-clausal-fo-noeq-uns.txt`
 * @param envVar       optional environment variable naming a file to use instead of the packaged resource
 */
final class ProblemList(val listFileName: String, envVar: Option[String] = None):

  /** Resource path of the packaged list. */
  private def resourcePath: String = s"/lisa/automation/superposition/$listFileName"

  /** The env-var override, when set and pointing at a readable file. Lets a harness run against a hand-made
    * list, a regression subset say, without rebuilding. */
  private def overrideFile: Option[File] = envVar.flatMap(sys.env.get).map(new File(_)).filter(_.isFile)

  /** Whether the list can be read at all, whether the override or the packaged resource. */
  def exists: Boolean = overrideFile.isDefined || getClass.getResource(resourcePath) != null

  /** Where the list came from, for the harness banner. */
  def describe: String = overrideFile.map(_.getPath).getOrElse(s"classpath:$resourcePath")

  /** Every problem path, in file order. Throws if neither the override nor the resource can be read. */
  lazy val all: Vector[String] =
    def read(source: scala.io.Source): Vector[String] =
      Using(source)(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get
    overrideFile.map(f => read(scala.io.Source.fromFile(f))) match
      case Some(lines) => lines
      case None =>
        Option(getClass.getResourceAsStream(resourcePath)) match
          case Some(in) => read(scala.io.Source.fromInputStream(in))
          case None =>
            throw new java.io.FileNotFoundException(
              s"Problem list $listFileName is on neither the classpath ($resourcePath) nor " +
                envVar.fold("any override (this list has no env-var override)")(v => s"$$$v"))

  /** A reproducible sample of `n` problems drawn with `seed`: the same seed always picks the same problems,
    * and an `n` past the end of the list returns the whole shuffled list. */
  def sample(n: Int = 100, seed: Long = 42): Vector[String] =
    new scala.util.Random(seed).shuffle(all).take(n)

/**
 * Small helpers shared by the benchmark / evaluation entry points ([[Evaluation]], [[FofEvaluation]],
 * [[EqFofEvaluation]], [[BaselineBench]], [[StrategyEvaluation]]): the TPTP-root lookup, the interruptible
 * worker with its abandoned-worker accounting, and the kernel-problem conversion, so each `main` does not
 * carry its own copy.
 */
object BenchUtil:

  /** The TPTP root from the `TPTP` environment variable, or `None` after printing the standard hint, since
    * every harness is a `main` and this is the one setup mistake they all hit. */
  def tptpRootOrExplain(): Option[File] =
    val root = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)
    if root.isEmpty then
      println("Set the TPTP environment variable to the TPTP root (the directory containing Problems/).")
    root

  /** How long [[withTimeout]] waits, after interrupting, for a worker to notice and unwind. Interruption is
    * cooperative: the solver polls a deadline and `checkInterrupted` polls the flag, so a worker between two
    * poll points needs a moment. Long enough for that, short enough not to stall a run. */
  private val interruptGraceMs: Long = 2000L

  private val abandoned = new java.util.concurrent.atomic.AtomicInteger(0)

  /** Workers that ignored their interrupt and were still running when [[withTimeout]] gave up, since the last
    * [[resetAbandoned]]. Anything measured after the first one is suspect: an abandoned worker keeps burning
    * CPU and holding its heap (a saturation's passive set can be millions of clauses) for the rest of the
    * run, so later problems are timed against a machine that is busy and nearly out of memory, and
    * `Clausification.checkInterrupted`'s heap valve, which is global, can abort them outright. Observed
    * turning a 44-refutation run into a 20-refutation one, with problems that refute standalone in 6 ms
    * reported as `TIMEOUT`. There is no safe way to kill a thread on the JVM, so the harnesses report this
    * rather than pretend it did not happen. */
  def abandonedWorkers: Int = abandoned.get

  /** Zero the [[abandonedWorkers]] count; call at the start of a benchmark run. */
  def resetAbandoned(): Unit = abandoned.set(0)

  /** A one-line warning naming the contamination, or `""` when the run was clean. */
  def contaminationWarning: String =
    val n = abandonedWorkers
    if n == 0 then ""
    else
      s"!! $n worker${if n == 1 then "" else "s"} ignored the interrupt and kept running. Every result after " +
        "the first is suspect: that thread holds CPU and heap for the rest of the run. Re-run the affected " +
        "problems on their own before believing any of these numbers."

  /** Run `body` on a daemon thread; return its outcome, or `None` if it doesn't finish within `ms`.
   *
   *  On a timeout the worker is interrupted and then given [[interruptGraceMs]] to unwind, so the common case
   *  (a solver that notices at its next poll) really is finished before the caller moves on. One that is
   *  still alive after the grace period cannot be stopped (`Thread.stop` is gone, and unsafe when it existed)
   *  and is counted in [[abandonedWorkers]] for the harness to report. */
  def withTimeout[T](ms: Long)(body: => T): Option[Try[T]] =
    val box = new AtomicReference[Option[Try[T]]](None)
    val th = new Thread(() => box.set(Some(Try(body))))
    th.setDaemon(true); th.start(); th.join(ms)
    if !th.isAlive then box.get()
    else
      th.interrupt()
      th.join(interruptGraceMs) // give the cooperative poll points a chance to fire
      if th.isAlive then abandoned.incrementAndGet()
      // `None` unconditionally, even though a worker that unwound during the grace period has by now stored
      // its `Failure(InterruptedException)`. The budget was exceeded; that is the verdict, and the exception
      // is just how the worker was stopped. Returning it would reclassify every `HARD_TIMEOUT` as an `ERROR`.
      None

  // ── running one problem in its own JVM ──────────────────────────────────────────────────────────────────
  //
  // Why a process and not a thread. A thread can only be *asked* to stop: interruption is cooperative, and
  // `Thread.stop` was removed (it threw `ThreadDeath` at an arbitrary bytecode boundary, leaving locks and
  // invariants broken). A worker that does not stop keeps its heap (a saturation's passive set can be
  // millions of clauses) and its CPU for the rest of the run, so every problem measured afterwards is timed
  // against a busy, nearly-full JVM, and `Clausification.checkInterrupted`'s heap ceiling, which is
  // JVM-global, can abort them outright. That turned a 44-refutation corpus run into a 20-refutation one,
  // reporting problems that refute standalone in 6 ms as `TIMEOUT` (see the code review, §4.4).
  //
  // A child process ends that whole class of problem: `destroyForcibly` is unconditional, so the budget is a
  // real guarantee; the heap dies with the process, so no problem inherits another's garbage, GC state or
  // static fields; and a fatal `OutOfMemoryError`/`StackOverflowError` kills only that problem.
  //
  // The cost is JVM startup plus JIT warm-up per problem, which for a problem that solves in 5 ms dominates
  // its measurement completely. Verdicts (did it refute?) are unaffected and are what corpus runs turn on;
  // per-problem *timings* on fast problems are not comparable to in-process ones. Set `LISA_FORK=0` to fall
  // back to the in-process path when that matters.

  /** Whether harnesses should run each problem in its own JVM. On unless `LISA_FORK` is `0`/`false`/`no`. */
  def forkEnabled: Boolean =
    !sys.env.get("LISA_FORK").map(_.trim.toLowerCase).exists(Set("0", "false", "no"))

  /** What became of a forked child: its exit code, whether we had to kill it, and what it printed. */
  final case class ForkOutcome(exitCode: Int, timedOut: Boolean, stdout: Vector[String], stderr: Vector[String]):
    /** The single `RESULT\t…` line a child prints, if it got that far. Absent means it died first, killed on
      * timeout, or a fatal error no `catch` inside the child could report. */
    def resultLine: Option[String] = stdout.find(_.startsWith(ResultPrefix))
    /** Why a child that printed no result died, for the harness's row. Empty when we killed it, since the row's
      * category already says `HARD_TIMEOUT`, and repeating it in the detail column tells the reader nothing.
      * For a crash it carries the exit code and the child's last stderr line, which is usually the whole
      * diagnosis (`java.lang.OutOfMemoryError: Java heap space`). */
    def crashDetail: String =
      if timedOut then ""
      else s"exit=$exitCode${stderr.reverseIterator.find(_.trim.nonEmpty).map(l => s", ${l.trim}").getOrElse("")}"

  /** The marker a child prints its one machine-readable result line with. */
  val ResultPrefix: String = "RESULT\t"

  /** Run `mainClass args` in a fresh JVM, with the same java binary, classpath and max heap as this one, and give it
    * `timeoutMs` to finish before killing it outright.
    *
    * Streams are redirected to temp files rather than pipes: a child that outproduces the pipe buffer while
    * nobody is draining it would block forever, which is exactly the hang this is meant to prevent. */
  def runForked(mainClass: String, args: Seq[String], timeoutMs: Long): ForkOutcome =
    val javaBin = new File(new File(System.getProperty("java.home"), "bin"),
      if System.getProperty("os.name").toLowerCase.contains("win") then "java.exe" else "java").getPath
    val heapMb = math.max(64L, Runtime.getRuntime.maxMemory / (1024 * 1024))
    // `-cp` on the command line: this project's classpath is a few KB, well inside the ~32 KB limit Windows
    // imposes. A much longer one would need an `@argfile` (and its backslash-escaping rules).
    val cmd = new java.util.ArrayList[String]()
    List(javaBin, "-cp", System.getProperty("java.class.path"), s"-Xmx${heapMb}m", mainClass).foreach(cmd.add)
    args.foreach(cmd.add)
    val out = File.createTempFile("lisa-fork-", ".out")
    val err = File.createTempFile("lisa-fork-", ".err")
    try
      val p = new ProcessBuilder(cmd).redirectOutput(out).redirectError(err).start()
      p.getOutputStream.close() // the child never reads stdin; leaving it open can wedge one that tries
      val finished = p.waitFor(timeoutMs, java.util.concurrent.TimeUnit.MILLISECONDS)
      if !finished then
        p.destroyForcibly()
        p.waitFor(10, java.util.concurrent.TimeUnit.SECONDS) // reap it; SIGKILL, so this returns at once
      def lines(f: File): Vector[String] =
        if !f.isFile then Vector.empty
        else Using(scala.io.Source.fromFile(f))(_.getLines().toVector).getOrElse(Vector.empty)
      ForkOutcome(if finished then p.exitValue else -1, !finished, lines(out), lines(err))
    finally { out.delete(); err.delete() }

  /** Pull hypotheses + conjecture from a parsed TPTP problem (axiom-like roles → LHS-free hypotheses). */
  def toClausificationProblem(p: Problem): Clausification.Problem =
    val hyps = p.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if axiomLikeRoles.contains(s.role) => s.sequent
    }
    val conj = p.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if s.role == "conjecture" => s.sequent
    }
    Clausification.Problem(hyps, conj)

  /** Upper median of `xs` (the upper of the two middles when even; `0.0` if empty). */
  def median(xs: Seq[Double]): Double = if xs.isEmpty then 0.0 else xs.sorted.apply(xs.size / 2)
