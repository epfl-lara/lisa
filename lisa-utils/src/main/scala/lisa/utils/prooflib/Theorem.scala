package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.collection.Extensions._
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.Helpers.withParams

sealed trait TheoremKind:
  /**
   * Proves a runtime-generated theorem under a fresh name derived from its source location.
   */
  def generated(using
      library: Library,
      output: OutputManager,
      file: sourcecode.File,
      line: sourcecode.Line,
      fullName: sourcecode.FullName
  )(statement: Sequent)(computeProof: ProofBuilder ?=> Any): Theorem =
    named(library.theorems.freshName(fullName.value))(statement)(computeProof)

  /**
   * Declares a theorem with an explicit name for generated developments.
   */
  def named(using library: Library, output: OutputManager, file: sourcecode.File, line: sourcecode.Line)(fullName: String)(statement: Sequent)(computeProof: ProofBuilder ?=> Any): Theorem =
    apply(using library, output, file, line, sourcecode.FullName(fullName), sourcecode.Name(fullName.split('.').last))(statement)(computeProof)

  def apply(using
      library: Library,
      output: OutputManager,
      sourceFile: sourcecode.File,
      sourceLine: sourcecode.Line,
      fullName: sourcecode.FullName,
      name: sourcecode.Name
  )(statement: Sequent)(computeProof: ProofBuilder ?=> Any): Theorem =
    def newCompute(using proof: ProofBuilder): ProofCarrier[?] =
      computeProof(using proof) match
        case carrier: ProofCarrier[?] => carrier
        case thm: Thm => ProofJudgement(thm)
        case _ => proof.pure(())
    new Theorem(this)(using library, output)(sourceFile, sourceLine, fullName, name)(statement)(newCompute)

case object Theorem extends TheoremKind:
  given asThm: Conversion[Theorem, Thm] = _.thm
  given asKernel: Conversion[Theorem, K.Thm] = _.kernel

case object Lemma extends TheoremKind

final class Theorem(theoremKind: TheoremKind)(using library: Library, output: OutputManager)(
    val file: sourcecode.File,
    val line: sourcecode.Line,
    val fullName: sourcecode.FullName,
    val name: sourcecode.Name
)(val statement: Sequent)(computeProof: ProofBuilder ?=> ProofCarrier[?]):
  val kind: TheoremKind = theoremKind
  val shortName: String =
    fullName.value.split('.').lastOption.getOrElse(name.value)

  val judgement: ProofJudgement =
    val underlyingGoal = statement.underlying
    val proof = ProofBuilder.withGoal(statement)
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
                .fold(
                  _ =>
                    // weakening failed
                    val error = SoftError(
                      withParams("The proven statement is not the same as the goal and cannot be weakened to it.", "Proven" -> inner.statement, "Goal" -> statement),
                      file,
                      line
                    )
                    inner.judgement.withError(error)
                  ,
                  // weakening succeeded
                  thm => inner.judgement.withJustification(Thm(statement, thm))
                )
            case None =>
              inner.judgement

  val innerThm: Thm = judgement.destruct._1
  def thm: Thm = innerThm
  def kernel: K.Thm = innerThm.kernel
  val errors: Set[ProofError] = judgement.errors

  def errorString(error: ProofError): String =
    val cwd = new java.io.File(".").getCanonicalPath
    val strippedFile = error.file.value.stripPrefix(cwd)
    s"\t$strippedFile:${error.line.value}: ${error.message}"

  def printState(): Unit =
    val state = s"  $kind $shortName := $statement"

    output.output(
      if errors.isEmpty then OutputManager.GREEN(state)
      else if thm.usesSorry then OutputManager.YELLOW(state)
      else OutputManager.RED(state)
    )

    errors.toSeq
      .sortBy(error => (error.file.value, error.line.value, error.message))
      .foreach:
        case error: SoftError =>
          output.output(OutputManager.YELLOW(errorString(error)))
        case error: FatalError =>
          output.output(OutputManager.RED(errorString(error)))

  // MUTABLY update the theorem registry
  library.theorems.register(this)

  printState()
