package lisa.maths.SetTheory.Types.ADTv2.support.core

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.{ProofTactic, UnapplicableProofTactic}

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

  def invalid[P <: lisa.utils.prooflib.Library#Proof](using
      lib: lisa.utils.prooflib.Library
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

  def attemptOrInvalid[P <: lisa.utils.prooflib.Library#Proof, A](using
      lib: lisa.utils.prooflib.Library
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

  def wrapUnapplicable[P <: lisa.utils.prooflib.Library#Proof, A](using
      lib: lisa.utils.prooflib.Library
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
