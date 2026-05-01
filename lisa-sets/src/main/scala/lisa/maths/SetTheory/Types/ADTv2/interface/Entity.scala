package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.**
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.renderAppliedSymbol
import lisa.utils.prooflib.ProofTacticLib.Arity

trait Entity[N <: Arity, Self <: Entity[N, Self]] {

  // ── Fields ────────────────────────────────────────────────────────────────

  protected def ownerKind: String
  def name: String
  def term: Expr[Ind]
  def typeVariables: Variable[Ind] ** N
  def typeVariablesSeq: Seq[Variable[Ind]]
  protected def rawSubstitutions: Seq[TypeSubstitution]
  protected def line: sourcecode.Line
  protected def file: sourcecode.File
  protected def rebuild(substitutions: Seq[TypeSubstitution]): Self

  final lazy val fullName: String = renderAppliedSymbol(
    name,
    typeVariablesSeq.size,
    resolvedTypeArguments(typeVariablesSeq, substitutions)
  )

  override final def toString: String = fullName

  // ── Substitution and specialization ───────────────────────────────────────

  final lazy val substitutions: Seq[TypeSubstitution] = normalizeTypeSubstitutions(
    ownerKind = ownerKind,
    ownerName = name,
    typeVariables = typeVariablesSeq,
    substitutions = rawSubstitutions
  )

  final lazy val remainingTypeVariables: Seq[Variable[Ind]] =
    getRemainingTypeVariables(
      typeVariablesSeq,
      substitutions
    )

  final def substitute(extraSubstitutions: TypeSubstitution*): Self =
    rebuild(substitutions ++ extraSubstitutions)

  final def specialize(args: Expr[Ind]*): Self = {
    val extraSubstitutions =
      substitutionsFromArgs(ownerKind, name, remainingTypeVariables, args)
    substitute(extraSubstitutions*)
  }

  // ── Lemmas ────────────────────────────────────────────────────────────────

  protected final def theoremName(suffix: String): String = s"$fullName/$suffix"

  protected final def specializeTheorem(baseTheorem: THM, suffix: String): THM = THM(
    quantifiedTypeStatement(
      baseTheorem.statement,
      typeVariablesSeq,
      substitutions,
      theoremName(suffix)
    ),
    theoremName(suffix),
    line.value,
    file.value,
    Theorem
  ) {
    have(baseTheorem.statement.substitute(substitutions*)) by
      Restate.from(baseTheorem.of(substitutions*))
    thenHave(thesis) by QuantifiersIntro(remainingTypeVariables)
  }

  // ── Apply ─────────────────────────────────────────────────────────────────

  final def apply(args: Expr[Ind]*): Self = {
    val completedSubstitutions =
      if args.isEmpty then substitutions
      else substitutions ++ substitutionsFromArgs(
        ownerKind = ownerKind,
        ownerName = name,
        typeVariables = remainingTypeVariables,
        args = args
      )

    rebuild(
      normalizeTypeSubstitutions(ownerKind, name, typeVariablesSeq, completedSubstitutions)
    )
  }

}
