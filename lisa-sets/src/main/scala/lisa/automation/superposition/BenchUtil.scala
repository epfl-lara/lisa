package lisa.automation.superposition

import java.io.File
import java.util.concurrent.atomic.AtomicReference
import scala.util.Try

import lisa.utils.K
import lisa.tptp.{Problem, AnnotatedFormula, AnnotatedSequent}
import lisa.tptp.KernelParser.axiomLikeRoles
import lisa.automation.clausification.Clausification

/**
 * Small helpers shared by the benchmark / evaluation entry points ([[Evaluation]], [[FofEvaluation]],
 * [[EqFofEvaluation]], [[BaselineBench]], [[StrategyEvaluation]]) — extracted here to
 * avoid the same handful of one-liners being copy-pasted into each `main`.
 */
object BenchUtil:

  /** Run `body` on a daemon thread; return its outcome, or `None` if it doesn't finish within `ms` (the worker is
   *  interrupted best-effort so the cooperatively-polling clausifier/solver can unwind). */
  def withTimeout[T](ms: Long)(body: => T): Option[Try[T]] =
    val box = new AtomicReference[Option[Try[T]]](None)
    val th = new Thread(() => box.set(Some(Try(body))))
    th.setDaemon(true); th.start(); th.join(ms)
    if th.isAlive then th.interrupt()
    box.get()

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

  /** Locate a generated problem-list file: the `envVar` override (if given and set) first, else the two
   *  source-relative paths, else the bare name in the cwd. `None` if none exists. Shared by every harness. */
  def locateList(listFileName: String, envVar: Option[String] = None): Option[File] =
    val candidates: List[File] =
      envVar.flatMap(sys.env.get).map(new File(_)).toList :::
        List(
          s"lisa-sets/src/main/scala/lisa/automation/superposition/$listFileName",
          s"src/main/scala/lisa/automation/superposition/$listFileName",
          listFileName
        ).map(new File(_))
    candidates.find(_.isFile)
