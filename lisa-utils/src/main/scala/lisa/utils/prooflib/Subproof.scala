package lisa.utils.prooflib

import lisa.utils.LisaException

import scala.util.boundary
import scala.util.boundary.Label
import scala.util.boundary.break
import scala.util.control.NonFatal

case class SubproofLabel[T](private val inner: Label[ProofCarrier[T]]):
  def breakWith(judgment: ProofCarrier[T]): Nothing =
    break(judgment)(using inner)

object SubproofM:
  private[prooflib] def run[T](isTactic: Boolean)(using
      library: Library
  )(inner: ProofBuilder ?=> SubproofLabel[T] ?=> ProofCarrier[T])(using
      file: sourcecode.File,
      line: sourcecode.Line
  ): ProofCarrier[T] =
    ProofBuilder.freshContext(isTactic): proof ?=>
      boundary: label ?=>
        if !isTactic then inner(using proof)(using SubproofLabel(label))
        else
          try inner(using proof)(using SubproofLabel(label))
          catch
            case error: TacticException => throw error
            case NonFatal(error: Exception) if !error.isInstanceOf[boundary.Break[?]] =>
              error match
                case lisaError: LisaException => throw new TacticException(lisaError.showError, lisaError)(using lisaError.line, lisaError.file)
                case _ => throw new TacticException(Option(error.getMessage).getOrElse(error.getClass.getName), error)

  /**
   * Runs a subproof isolated from the current local proof context.
   */
  def apply[T](using library: Library)(inner: ProofBuilder ?=> SubproofLabel[T] ?=> ProofCarrier[T]): ProofCarrier[T] =
    run(isTactic = false)(inner)

object Subproof:
  private[prooflib] def maybeWrap(inner: ProofBuilder ?=> SubproofLabel[Unit] ?=> (Thm | ProofJudgement)): ProofBuilder ?=> SubproofLabel[Unit] ?=> ProofCarrier[Unit] = ip ?=>
    sp ?=>
      inner match
        case thm: Thm => ProofJudgement(thm)
        case judgement: ProofJudgement => judgement

  /**
   * Runs a subproof isolated from the current local proof context.
   */
  def apply(using library: Library)(inner: ProofBuilder ?=> SubproofLabel[Unit] ?=> (Thm | ProofJudgement)): ProofCarrier[Unit] =
    SubproofM(using library)(pr ?=> ((sl: SubproofLabel[Unit]) ?=> maybeWrap(inner)))

/**
 * Runs an independent tactic proof, classifying escaping exceptions without admitting failed steps.
 */
object TacticProof:
  /**
   * Creates a tactic builder and returns the theorem or expected failure produced by the block.
   */
  def apply(using
      library: Library
  )(inner: ProofBuilder ?=> SubproofLabel[Unit] ?=> (Thm | ProofJudgement))(using
      sourcecode.File,
      sourcecode.Line
  ): ProofJudgement =
    SubproofM.run(isTactic = true)(Subproof.maybeWrap(inner))

/**
 * Runs an independent tactic proof with a computed payload, classifying escaping exceptions.
 */
object TacticProofM:
  /**
   * Creates a tactic builder and supports early failure through `failWith`.
   */
  def apply[T](using
      library: Library
  )(inner: ProofBuilder ?=> SubproofLabel[T] ?=> ProofCarrier[T])(using
      sourcecode.File,
      sourcecode.Line
  ): ProofCarrier[T] =
    SubproofM.run(isTactic = true)(inner)
