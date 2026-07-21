package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.*
import lisa.utils.collection.Extensions.*
import lisa.utils.prooflib.Helpers.withParams

sealed trait TheoremKind:
  def apply(using library: Library, output: OutputManager, sourceFile: sourcecode.File, sourceLine: sourcecode.Line, fullName: sourcecode.FullName, name: sourcecode.Name)(statement: Sequent)(computeProof: Proof ?=> Any): Theorem =
    def carrier(using proof: Proof): ProofCarrier[?] =
      computeProof(using proof) match
        case carrier: ProofCarrier[?] => carrier
        case _ => proof.pure(())
    new Theorem(this)(using library, output)(sourceFile, sourceLine, fullName, name)(statement)(carrier)

case object Theorem extends TheoremKind:
  given asThm: Conversion[Theorem, Thm] = _.thm
  given asKernel: Conversion[Theorem, K.Thm] = _.kernel

case object Lemma extends TheoremKind

final class Theorem 
  (theoremKind: TheoremKind)
  (using library: Library, output: OutputManager)
  (val file: sourcecode.File, val line: sourcecode.Line, val fullName: sourcecode.FullName, val name: sourcecode.Name)
  (val Statement: Sequent)
  (computeProof: Proof ?=> ProofCarrier[?]):
  val kind: TheoremKind = theoremKind
  val shortName: String = 
    fullName.value.split('.').lastOption.getOrElse(name.value)
  val statement: Sequent = Statement

  val judgement: ProofJudgement = 
    val underlyingGoal = statement.underlying
    val proof = Proof.withGoal(statement)
    val inner = computeProof(using proof).withErrors(proof.errors)
    inner match
      case inner: FatalCarrier =>
        // a theorem is a closed context, so a fatal error is recoverable
        inner.recoverWith(statement)
      case inner: SoftCarrier[_] =>
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
                  thm => inner.judgement.withJustification(Thm(statement, thm))
                )
            case None =>
              inner.judgement

  val innerThm: Thm = judgement.destruct._1
  def thm: Thm = innerThm.copy(isSchema = true)
  def kernel: K.Thm = innerThm.kernel
  val errors: Set[ProofError] = judgement.errors

  // MUTABLY update the theorem registry
  library.theorems.register(this)

  private val state = s"  $kind $shortName := $statement"
  output.output(if errors.isEmpty then OutputManager.GREEN(state) else OutputManager.RED(state))
  errors.toSeq
    .sortBy(error => (error.file.value, error.line.value, error.message))
    .foreach(error => output.output(OutputManager.RED(s"    ${error.file.value}:${error.line.value}: ${error.message}")))

  // TODO: if errors.nonEmpty and strict mode?
