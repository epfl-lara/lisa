package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.ADTv2.encoding.**
import lisa.maths.SetTheory.Types.ADTv2.recursion.RecFunSemantics
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.*
import lisa.utils.prooflib.ProofTacticLib.Arity

class RecFunction[N <: Arity](using protected val line: sourcecode.Line, protected val file: sourcecode.File)(
    val semantic: RecFunSemantics[N],
    private val adt: ADT[N],
    protected val rawSubstitutions: Seq[TypeSubstitution] = Nil
) extends Entity[N, RecFunction[N]] {

  // ── Fields ────────────────────────────────────────────────────────────────

  protected final val ownerKind: String = "RecFunction"

  final val name: String = semantic.name

  final val typeVariables: Variable[Ind] ** N = semantic.typeVariables

  final val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq

  final lazy val term: Expr[Ind] =
    semantic.term(resolvedTypeArguments(typeVariablesSeq, substitutions))

  final lazy val argType: Expr[Ind] = semantic.argType.substitute(substitutions*)

  final lazy val returnType: Expr[Ind] = semantic.returnType.substitute(substitutions*)

  final lazy val typ: Expr[Ind] = semantic.typ.substitute(substitutions*)

  private lazy val specializedADT =
    if adt.substitutions == substitutions then adt
    else new ADT[N](adt.semantic, substitutions)

  final infix def *(arg: Expr[Ind]): Expr[Ind] = app(term)(arg)

  // ── Lemmas ────────────────────────────────────────────────────────────────

  /** Lemma - typing of the recursive-function head specialized with the current type substitutions. */
  final lazy val intro: THM = specializeTheorem(semantic.intro, "introduction")

  /** Lemma - applied recursive-function typing rule in sequent form for the current type substitutions. */
  final lazy val introApp: THM = Theorem(using name = sourcecode.FullName(s"$fullName/introApp"))(
    Set(RecFunction.introAppVariable :: argType) |- (
      app(term)(RecFunction.introAppVariable) :: returnType
    )
  ) {
    have(semantic.intro.statement.substitute(substitutions*)) by
      Restate.from(semantic.intro.of(substitutions*))

    val appliedTyping = proveAppliedTyping(
      headTyping = lastStep,
      headTerm = term,
      headType = typ,
      args = Seq(RecFunction.introAppVariable -> argType)
    )

    have(thesis) by Tautology.from(appliedTyping)
  }

  /** Lemma - recursive equations specialized with the current type substitutions, one per constructor case. */
  final lazy val elim: Map[Constructor[N], THM] = specializedADT.constructors.map(c =>
    c -> specializeTheorem(
      semantic.shortDefinition(c.semantic),
      s"elimination: ${c.fullName} case"
    )
  ).toMap

  // ── Apply ─────────────────────────────────────────────────────────────────

  protected final def rebuild(substitutions: Seq[TypeSubstitution]): RecFunction[N] =
    new RecFunction[N](semantic, adt, substitutions)

  final lazy val debug_uniqueness: THM = semantic.uniqueness
  final lazy val debug_classDefinitionFact: THM = semantic.classDefinitionFact
}

object RecFunction {
  def selfReferenceName(functionName: String): String = s"${functionName}RecSelf"

  def selfPlaceholder(functionName: String): Variable[Ind] =
    Variable[Ind](selfReferenceName(functionName))

  private[ADTv2] val introAppVariable: Variable[Ind] =
    Variable[Ind]("recFunctionArg")
}
