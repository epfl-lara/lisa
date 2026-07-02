package lisa.utilcfs.prooflib

import scala.annotation.targetName

object TacticM:
  def apply[T](using proof: Proof)(run: Proof ?=> ProofCarrier[T]): ProofCarrier[T] =
    proof.withSubcontext()(run)

  @targetName("applyPure")
  def apply[T](using proof: Proof)(run: Proof ?=> T): Proof ?=> ProofCarrier[T] =
    val result = run(using proof)
    proof.pure(result)

object Tactic:
  def apply(using proof: Proof)(run: Proof ?=> ProofJudgement): ProofJudgement =
    TacticM(proof ?=> run(using proof))

  @targetName("applyPure")
  def apply(using proof: Proof)(run: Proof ?=> Unit): ProofJudgement =
    TacticM(proof ?=> run(using proof))
