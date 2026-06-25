package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.collection.Extensions.*
import lisa.utilcfs.prooflib.Helpers.withParams

sealed trait TheoremKind:
  def apply(using library: Library, sourceFile: sourcecode.File, sourceLine: sourcecode.Line, fullName: sourcecode.FullName, name: sourcecode.Name)(statement: Sequent)(computeProof: Proof ?=> ProofJudgement): Theorem =
    new Theorem(this)(using library)(sourceFile, sourceLine, fullName, name)(statement)(computeProof)

case object Theorem extends TheoremKind
case object Lemma extends TheoremKind

final class Theorem 
  (theoremKind: TheoremKind)
  (using library: Library)
  (sourceFile: sourcecode.File, sourceLine: sourcecode.Line, fullName: sourcecode.FullName, name: sourcecode.Name)
  (statement: Sequent)
  (computeProof: Proof ?=> ProofCarrier[?]):
  val judgement: ProofJudgement = 
    val underlyingGoal = statement.underlying
    val proof = Proof.withGoal(underlyingGoal)
    val inner = computeProof(using proof).withErrors(proof.errors)
    // is the proven statement the actual goal or reduced to it trivially?
    if inner.statement == underlyingGoal then 
      // done
      inner.judgement
    else
      // try weakening, else fail softly
      inner.justification match
        case Some(thm) =>
          K.Weakening(using library.theory)(underlyingGoal, thm)
            .fold(_ =>
              // weakening failed
              val error = SoftError(withParams("The proven statement is not the same as the goal and cannot be weakened to it.", "Proven" -> inner.statement, "Goal" -> underlyingGoal), sourceFile, sourceLine)
              inner.judgement.withError(error),
              // weakening succeeded
              inner.judgement.withJustification
            )
        case None =>
          inner.judgement

  val innerThm: K.Thm = judgement.justification.getOrElse(K.sorry(using library.theory)(statement.underlying))
  val errors: Set[ProofError] = judgement.errors

  // TODO: if errors.nonEmpty and strict mode?
