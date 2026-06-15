package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedSemanticSignature
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.theoremAt
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{introAppAt => buildIntroAppAt}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.appSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.wellTypedSet
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

object SpecializedADT {
  given adtToSpecialized[N <: Arity](using sourcecode.Line, sourcecode.File): Conversion[ADT[N], SpecializedADT[N]] =
    adt => new SpecializedADT[N](adt, adt.typeVariablesSeq)
}

/**
 * User-facing instantiated view of a constructor.
 *
 * This is intentionally only an interface wrapper for now. The semantic specialized
 * domain layer can be introduced later if the recursive/proof internals need it.
 */
final class SpecializedConstructor[N <: Arity](using
    val line: sourcecode.Line,
    val file: sourcecode.File
)(
    val base: Constructor[N],
    val typeArgs: Seq[Expr[Ind]]
) {

  val name: String = base.name
  val fullName: String = base.semantic.fullName
  val typeVariables: Seq[Variable[Ind]] = base.typeVariablesSeq
  val term: Expr[Ind] = base.termAt(typeArgs)

  def intro: THM =
    theoremAt(name, base.typeVariablesSeq, typeArgs, "introduction", base.semantic.intro)

  def introApp: THM = buildIntroAppAt(
    displayName = name,
    typeVariables = base.typeVariablesSeq,
    typeArgs = typeArgs,
    baseTheorem = base.semantic.intro,
    headTermAt = _ => term,
    headTypeAt = substitutions => base.semantic.typ.substitute(substitutions*),
    assumptionsAt = substitutions => wellTypedSet(instantiatedSemanticSignature(base.semantic.semanticSignature, substitutions)),
    typingArgsAt = substitutions => instantiatedSemanticSignature(base.semantic.semanticSignature, substitutions),
    conclusionAt = substitutions =>
      base.semantic.appliedTerm.substitute(substitutions*) ::
        base.adt.term.substitute(substitutions*)
  )

  def injectivity: THM =
    theoremAt(name, base.typeVariablesSeq, typeArgs, "injectivity", base.semantic.injectivity)

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = appSeq(term)(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = applySeq(args)

  override def toString: String =
    renderAppliedSymbol(base.semantic.fullName, base.typeVariablesSeq.size, typeArgs)
}

/**
 * User-facing instantiated view of an ADT.
 *
 * This wrapper mirrors the non-specialized `ADT` API and gives a place to attach a
 * future specialized semantic domain if needed.
 */
final class SpecializedADT[N <: Arity](using
    val line: sourcecode.Line,
    val file: sourcecode.File
)(
    val base: ADT[N],
    val typeArgs: Seq[Expr[Ind]]
) {

  val name: String = base.name
  val typeVariables: Seq[Variable[Ind]] = base.typeVariablesSeq
  val term: Expr[Ind] = base.termAt(typeArgs)

  lazy val constructors: Seq[SpecializedConstructor[N]] =
    base.constructors.map(c => new SpecializedConstructor[N](c, typeArgs))

  def elim: THM =
    theoremAt(name, base.typeVariablesSeq, typeArgs, "elimination", base.semantic.elim)

  def induction: THM =
    theoremAt(name, base.typeVariablesSeq, typeArgs, "induction", base.semantic.induction)

  def injectivity(c1: SpecializedConstructor[N], c2: SpecializedConstructor[N]): THM =
    theoremAt(
      displayName = name,
      typeVariables = base.typeVariablesSeq,
      typeArgs = typeArgs,
      suffix = s"${c1.base.semantic.name}-${c2.base.semantic.name}/injectivity",
      baseTheorem = base.semantic.injectivity(c1.base.semantic, c2.base.semantic)
    )

  override def toString: String =
    renderAppliedSymbol(base.name, base.typeVariablesSeq.size, typeArgs)
}
