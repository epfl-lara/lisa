package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.{**, SemanticADT}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.*
import lisa.maths.SetTheory.Types.ADTv2.support.Printing
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.typeExprToTerm
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.utils.prooflib.ProofTacticLib.Arity

class ADT[N <: Arity](using protected val line: sourcecode.Line, protected val file: sourcecode.File)(
    val semantic: SemanticADT[N],
    protected val rawSubstitutions: Seq[TypeSubstitution] = Nil
) extends Entity[N, ADT[N]] {

  Printing.install()

  // ── Fields ────────────────────────────────────────────────────────────────

  protected final val ownerKind: String = "ADT"

  final val name: String = semantic.name

  final val id: Identifier = semantic.id

  final val typeVariables: Variable[Ind] ** N = semantic.typeVariables

  final val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq

  final lazy val term: Expr[Ind] =
    semantic.term(resolvedTypeArguments(typeVariablesSeq, substitutions))

  if substitutions.isEmpty then
    ADT.register(name, this)

  final lazy val constructors: Seq[Constructor[N]] =
    semantic.constructors.map(c => new Constructor[N](c, substitutions))

  // ── Lemmas ────────────────────────────────────────────────────────────────

  /** Lemma - structural induction principle specialized with the current type substitutions. */
  final lazy val induction: THM = specializeTheorem(semantic.induction, "induction")

  /** Lemma - elimination principle specialized with the current type substitutions. */
  final lazy val elim: THM = specializeTheorem(semantic.elim, "elimination")

  /** Lemma - disjointness of two distinct constructors under the current type substitutions. */
  final def injectivity(c1: Constructor[N], c2: Constructor[N]): THM = {
    val semanticLemma = semantic.injectivity(c1.semantic, c2.semantic)
    specializeTheorem(semanticLemma, s"${c1.semantic.name}-${c2.semantic.name}/injectivity")
  }

  // ── Apply ─────────────────────────────────────────────────────────────────

  protected final def rebuild(substitutions: Seq[TypeSubstitution]): ADT[N] =
    new ADT[N](semantic, substitutions)

  final def applyType(args: TypeExpr*): ADT[N] =
    apply(args.map(typeExprToTerm)*)
}

object ADT {
  private val namesToADT: scala.collection.mutable.Map[String, ADT[?]] =
    scala.collection.mutable.Map.empty

  private[ADTv2] def register(name: String, adt: ADT[?]): Unit =
    namesToADT.update(name, adt)

  def unapply(t: TypeRef): Option[ADT[?]] = getADT(t.name)

  def unapply(obj: TypeExpr): Option[(ADT[?], Seq[TypeExpr])] = obj match
    case TypeRef(name) => getADT(name).map((_, Seq.empty))
    case TypeApply(name, args) => getADT(name).map((_, args))

  def getADT(name: String): Option[ADT[?]] = namesToADT.get(name)

  def allADTs: Iterable[ADT[?]] = namesToADT.values
}
