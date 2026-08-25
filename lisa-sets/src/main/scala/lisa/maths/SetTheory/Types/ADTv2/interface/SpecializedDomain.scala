package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedSemanticSignature

import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.introAppTheorem
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.appSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.wellTypedSet
import lisa.maths.SetTheory.Types.TypingHelpers.::

object SpecializedADT {
  given adtToSpecialized[S](using sourcecode.Line, sourcecode.File): Conversion[ADT[S], SpecializedADT[S]] =
    adt => new SpecializedADT[S](adt, adt.typeVariablesSeq)
}

/**
 * User-facing instantiated view of a constructor.
 *
 * This is intentionally only an interface wrapper for now. The semantic specialized
 * domain layer can be introduced later if the recursive/proof internals need it.
 */
final class SpecializedConstructor[S](using
    val line: sourcecode.Line,
    val file: sourcecode.File
)(
    val base: Constructor[S],
    val typeArgs: Seq[Expr[Ind]]
) {

  val name: String = base.name
  val fullName: String = base.semantic.fullName
  val typeVariables: Seq[Variable[Ind]] = base.typeVariablesSeq
  val term: Expr[Ind] = base.termAt(typeArgs)

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
final class SpecializedADT[S](using
    val line: sourcecode.Line,
    val file: sourcecode.File
)(
    val base: ADT[S],
    val typeArgs: Seq[Expr[Ind]]
) {

  val name: String = base.name
  val typeVariables: Seq[Variable[Ind]] = base.typeVariablesSeq
  val term: Expr[Ind] = base.termAt(typeArgs)

  lazy val constructors: Seq[SpecializedConstructor[S]] =
    base.constructors.map(c => new SpecializedConstructor[S](c, typeArgs))

  override def toString: String =
    renderAppliedSymbol(base.name, base.typeVariablesSeq.size, typeArgs)
}
