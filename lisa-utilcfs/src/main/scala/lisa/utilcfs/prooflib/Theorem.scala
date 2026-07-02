package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.collection.Extensions.*
import lisa.utilcfs.prooflib.Helpers.withParams

sealed trait TheoremKind:
  def apply[T](using library: Library, sourceFile: sourcecode.File, sourceLine: sourcecode.Line, fullName: sourcecode.FullName, name: sourcecode.Name)(statement: Sequent)(computeProof: Proof ?=> T): Theorem =
    def carrier(using proof: Proof): ProofCarrier[?] =
      computeProof(using proof) match
        case carrier: ProofCarrier[?] => carrier
        case _ => proof.pure(())
    new Theorem(this)(using library)(sourceFile, sourceLine, fullName, name)(statement)(carrier)

case object Theorem extends TheoremKind:
  given Conversion[Theorem, Thm] = _.thm

case object Lemma extends TheoremKind

final class Theorem 
  (theoremKind: TheoremKind)
  (using library: Library)
  (val file: sourcecode.File, val line: sourcecode.Line, val fullName: sourcecode.FullName, val name: sourcecode.Name)
  (val Statement: Sequent)
  (computeProof: Proof ?=> ProofCarrier[?]):
  val kind: TheoremKind = theoremKind
  val shortName: String = 
    fullName.toString.split('.').lastOption.getOrElse(name.toString)
  val statement: Sequent = Statement

  val judgement: ProofJudgement = 
    val underlyingGoal = statement.underlying
    val proof = Proof.withGoal(underlyingGoal)
    val inner = computeProof(using proof).withErrors(proof.errors)
    // is the proven statement the actual goal or reduced to it trivially?
    if inner.statement.underlying == underlyingGoal then 
      // done
      inner.judgement
    else
      // try weakening, else fail softly
      inner.justification match
        case Some(thm) =>
          K.Weakening(using library.theory)(underlyingGoal, thm.kernel)
            .fold(_ =>
              // weakening failed
              val error = SoftError(withParams("The proven statement is not the same as the goal and cannot be weakened to it.", "Proven" -> inner.statement, "Goal" -> underlyingGoal), file, line)
              inner.judgement.withError(error),
              // weakening succeeded
              thm => inner.judgement.withJustification(Thm(thm))
            )
        case None =>
          inner.judgement

  val innerThm: Thm = judgement.destruct._1
  def thm: Thm = innerThm
  def kernel: K.Thm = innerThm.kernel
  val errors: Set[ProofError] = judgement.errors

  // MUTABLY update the theorem registry
  library.theorems.register(this)

  // TODO: if errors.nonEmpty and strict mode?
