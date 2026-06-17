package lisa.utilscfs.prooflib

import lisa.utilcfs.prooflib.Library

sealed trait TheoremError(msg: String) extends Exception

// TODO: add source code tracking
sealed trait TheoremKind:
  def apply(using library: Library)(statement: Sequent)(computeProof: Proof ?=> ProofJudgement): Theorem =
    new Theorem(this)(statement)(computeProof)
case object Theorem extends TheoremKind
case object Lemma extends TheoremKind

final class Theorem private (theoremKind: TheoremKind)(using library: Library)(statement: Sequent)(computeProof: Proof ?=> ProofJudgement):
  val judgement: ProofJudgement = 
    val inner = Proof.withContext(computeProof)
    val provenStatement = inner.statement
    if provenStatement != statement then
      if isSameSequent(provenSequent, statement) then
        // map over a restate step
        ???
      else
        // add an error
        ???
    else
      inner.judgement

  val (_, innerThm, errors, ()) = judgement.destruct

  // TODO: if errors.nonEmpty and strict mode?
