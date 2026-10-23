package lisa.utils.prooflib

import lisa.utils.fol.FOL.{Sequent, _}
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.ProofTacticLib.UnapplicableProofTactic

object TacticErrors {

  private def formatEntries(entries: Seq[(String, String)]): String =
    if entries.isEmpty then ""
    else
      entries.map { case (label, value) =>
        s"""$label:
           |  $value""".stripMargin
      }.mkString("\n\n")

  def message(
      tacticName: String,
      summary: String,
      factStatement: Sequent,
      bot: Sequent,
      entries: Seq[(String, String)] = Seq.empty
  ): String = {
    val entriesBlock = formatEntries(entries)
    val maybeEntries =
      if entriesBlock.isEmpty then ""
      else s"\n\n$entriesBlock"

    s"""$tacticName failed: $summary
       |
       |Original fact statement:
       |  $factStatement
       |
       |Requested goal:
       |  $bot$maybeEntries""".stripMargin
  }

  def invalid[P <: Library#Proof](using
      lib: Library,
      tactic: ProofTactic
  )(
      proof: P
  )(
      tacticName: String,
      summary: String,
      factStatement: Sequent,
      bot: Sequent,
      entries: (String, String)*
  ): proof.ProofTacticJudgement =
    proof.InvalidProofTactic(message(tacticName, summary, factStatement, bot, entries))

  def attemptOrInvalid[P <: Library#Proof, A](using
      lib: Library,
      tactic: ProofTactic
  )(
      proof: P
  )(
      tacticName: String,
      summary: String,
      factStatement: Sequent,
      bot: Sequent,
      entries: (String, String)*
  )(body: => A): Either[proof.ProofTacticJudgement, A] =
    try Right(body)
    catch
      case exception: UnapplicableProofTactic =>
        Left(invalid(using lib)(proof)(
          tacticName = tacticName,
          summary = summary,
          factStatement = factStatement,
          bot = bot,
          (entries :+ ("Underlying error" -> exception.getMessage))*
        ))

  def wrapUnapplicable[P <: Library#Proof, A](using
      lib: Library,
      currentTactic: ProofTactic
  )(
      proof: P
  )(
      tactic: ProofTactic,
      summary: String,
      factStatement: Sequent,
      bot: Sequent,
      entries: (String, String)*
  )(body: => A): A =
    try body
    catch
      case exception: UnapplicableProofTactic =>
        throw UnapplicableProofTactic(
          tactic,
          proof,
          message(
            tacticName = tactic.name,
            summary = summary,
            factStatement = factStatement,
            bot = bot,
            entries = entries :+ ("Underlying error" -> exception.getMessage)
          )
        )
}
