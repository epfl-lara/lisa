package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.{**, SemanticConstructor}
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.{FunctionalClass, TypedConstantFunctional}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.wellTypedSet
import lisa.utils.prooflib.ProofTacticLib.Arity

class Constructor[N <: Arity](using protected val line: sourcecode.Line, protected val file: sourcecode.File)(
    val semantic: SemanticConstructor[N],
    protected val rawSubstitutions: Seq[TypeSubstitution] = Nil
) extends TypedConstantFunctional[Ind](
      semantic.fullName,
      FunctionalClass(
        Nil,
        Nil,
        semantic.typ.substitute(
          normalizeTypeSubstitutions(
            ownerKind = "Constructor",
            ownerName = semantic.fullName,
            typeVariables = semantic.typeVariablesSeq,
            substitutions = rawSubstitutions
          )*
        )
      ),
      semantic.intro
    ) with Entity[N, Constructor[N]] {

  // ── Fields ────────────────────────────────────────────────────────────────

  protected final val ownerKind: String = "Constructor"

  final val name: String = semantic.fullName

  final val typeVariables: Variable[Ind] ** N = semantic.typeVariables

  final val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq

  final lazy val term: Expr[Ind] =
    semantic.term(resolvedTypeArguments(typeVariablesSeq, substitutions))

  private lazy val specializedHeadType: Expr[Ind] = semantic.typ.substitute(substitutions*)

  // ── Lemmas ────────────────────────────────────────────────────────────────

  /** Lemma - typing of the constructor head specialized with the current type substitutions. */
  final lazy val intro: THM = specializeTheorem(semantic.intro, "introduction")

  /** Lemma - applied constructor typing rule in sequent form for the current type substitutions. */
  final lazy val introApp: THM = Theorem(using name = sourcecode.FullName(s"$fullName/introApp"))(
    wellTypedSet(
      instantiatedSemanticSignature(semantic.semanticSignature, substitutions)
    ) |- (
      specializeTerm(semantic.appliedTerm, substitutions) ::
        specializeTerm(semantic.adt.term, substitutions)
    )
  ) {
    have(semantic.intro.statement.substitute(substitutions*)) by
      Restate.from(semantic.intro.of(substitutions*))

    val appliedTyping = proveAppliedTyping(
      headTyping = lastStep,
      headTerm = term,
      headType = specializedHeadType,
      args = instantiatedSemanticSignature(semantic.semanticSignature, substitutions)
    )

    have(thesis) by Tautology.from(appliedTyping)
  }

  /** Lemma - injectivity of the constructor specialized with the current type substitutions. */
  final lazy val injectivity: THM = specializeTheorem(semantic.injectivity, "injectivity")

  // ── Apply ─────────────────────────────────────────────────────────────────

  protected final def rebuild(substitutions: Seq[TypeSubstitution]): Constructor[N] =
    new Constructor[N](semantic, substitutions)
}
