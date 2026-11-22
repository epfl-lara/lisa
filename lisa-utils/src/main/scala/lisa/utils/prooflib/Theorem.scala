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
        case _ =>
          if proof.last.isEmpty then throw new UnimplementedProof(fullName.value, statement)(using sourceLine, sourceFile)
          proof.pure(())
    new Theorem(this)(using library, output)(sourceFile, sourceLine, fullName, name)(statement)(newCompute)

case object Theorem extends TheoremKind:
  given asThm: Conversion[Theorem, Thm] = _.thm
  given asKernel: Conversion[Theorem, K.Thm] = _.kernel

case object Lemma extends TheoremKind

/**
 * Declares a theorem using the corollary label.
 */
case object Corollary extends TheoremKind

final class Theorem(theoremKind: TheoremKind)(using library: Library, output: OutputManager)(
    val file: sourcecode.File,
    val line: sourcecode.Line,
    val fullName: sourcecode.FullName,
    val name: sourcecode.Name
)(val statement: Sequent)(computeProof: ProofBuilder ?=> ProofCarrier[?]):
  val kind: TheoremKind = theoremKind
  val shortName: String =
    fullName.value.split('.').lastOption.getOrElse(name.value)

  private val proof = ProofBuilder.withGoal(statement, isTactic = false)

  val judgement: ProofJudgement =
    proof.recover(statement) {
      computeProof(using proof).flatMap { (_, theorem) =>
        if theorem.kernel.assumptions.nonEmpty then
          ProofCarrier.Failure(
            withParams(
              "The proof has unresolved kernel assumptions.",
              "Unresolved proof assumptions" -> theorem.kernel.assumptions.iterator.map(Thm.liftSequent).map(_.toString).toSeq.sorted.mkString("\n")
            )
          )
        else if theorem.statement.underlying == statement.underlying then ProofJudgement(Thm(statement, theorem.kernel))
        else
          K.Weakening(using library.theory)(statement.underlying, theorem.kernel)
            .fold(
              _ => ProofCarrier.Failure(withParams("The proven statement is not the same as the goal and cannot be weakened to it.", "Proven" -> theorem.statement, "Goal" -> statement)),
              kernel => ProofJudgement(Thm(statement, kernel))
            )
      }
    }(using file, line)

  val innerThm: Thm = judgement.destruct._1
  def thm: Thm = innerThm
  def kernel: K.Thm = innerThm.kernel
  val errors: Vector[ProofDiagnostic] = proof.errors.toVector

  def printState(): Unit =
    val state = s"  $kind $shortName := $statement"

    if errors.nonEmpty then output.error(OutputManager.RED(state))
    else
      output.output(
        if thm.usesSorry then OutputManager.YELLOW(s"$state (Relies on Sorry)")
        else OutputManager.GREEN(state)
      )

    errors.foreach { error =>
      val (header, body) = error.format.span(_ != '\n')
      output.error(OutputManager.RED(header) + body + "\n")
    }

  // MUTABLY update the theorem registry
  library.theorems.register(this)

  printState()
