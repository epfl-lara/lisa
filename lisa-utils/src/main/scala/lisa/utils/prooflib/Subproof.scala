package lisa.utils.prooflib

import scala.util.boundary
import scala.util.boundary.Label
import scala.util.boundary.break

case class SubproofLabel[T](private val inner: Label[ProofCarrier[T]]):
  def breakWith(judgment: ProofCarrier[T]): Nothing =
    break(judgment)(using inner)

object SubproofM:
  private def run[T](using library: Library, proof: Proof)(inner: Proof ?=> SubproofLabel[T] ?=> ProofCarrier[T]): ProofCarrier[T] =
    boundary: label ?=>
      inner(using proof)(using SubproofLabel(label))

  /**
   * Runs a subproof isolated from the current local proof context.
   */
  def apply[T](using library: Library)(inner: Proof ?=> SubproofLabel[T] ?=> ProofCarrier[T]): ProofCarrier[T] =
    Proof.withContext: subproof ?=>
      run(using library, subproof)(inner)

object Subproof:
  private def maybeWrap(using Library)(inner: Proof ?=> SubproofLabel[Unit] ?=> (Thm | ProofJudgement)): Proof ?=> SubproofLabel[Unit] ?=> ProofCarrier[Unit] = ip ?=>
    sp ?=>
      inner match
        case thm: Thm => ProofJudgement(thm)
        case judgement: ProofJudgement => judgement

  /**
   * Runs a subproof isolated from the current local proof context.
   */
  def apply[T](using library: Library)(inner: Proof ?=> SubproofLabel[Unit] ?=> (Thm | ProofJudgement)): ProofCarrier[Unit] =
    SubproofM(using library)(pr ?=> ((sl: SubproofLabel[Unit]) ?=> maybeWrap(using library)(inner)))
