package lisa.utilcfs.prooflib

import scala.util.boundary
import scala.util.boundary.{break, Label}

case class SubproofLabel[T](private val inner: Label[ProofCarrier[T]]):
  def breakWith(judgment: ProofCarrier[T]): Nothing =
    break(judgment)(using inner)

object SubproofM:
  private def run[T](using library: Library, proof: Proof)(inner: Proof ?=> SubproofLabel[T] ?=> ProofCarrier[T]): ProofCarrier[T] =
    boundary: label ?=>
      inner(using proof)(using SubproofLabel(label))

  /** Runs a subproof isolated from the current local proof context. */
  def apply[T](using library: Library)(inner: Proof ?=> SubproofLabel[T] ?=> ProofCarrier[T]): ProofCarrier[T] =
    Proof.withContext: subproof ?=>
      run(using library, subproof)(inner)

object Subproof:
  /** Runs a subproof isolated from the current local proof context. */
  def apply[T](using library: Library)(inner: Proof ?=> SubproofLabel[Unit] ?=> Thm): ProofCarrier[Unit] =
    SubproofM(using library)(pr ?=> ((sl: SubproofLabel[Unit]) ?=> ProofJudgement(inner)))
