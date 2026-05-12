package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.{**, toSeq}
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.{FunctionalClass, TypedConstantFunctional}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{instantiatedSemanticSignature, introAppAt as buildIntroAppAt, requireMonomorphicAccess, theoremAt}
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.{renderAppliedSymbol, wellTypedSet}
import lisa.utils.prooflib.ProofTacticLib.Arity

final class Constructor[N <: Arity](using val line: sourcecode.Line, val file: sourcecode.File, valueOfN: ValueOf[N])(
    val semantic: SemanticConstructor[N]
) extends TypedConstantFunctional[IndOf[N]](
      semantic.id,
      FunctionalClass(
        List.fill(semantic.typeVariablesSeq.size)(None), 
        semantic.typeVariablesSeq.toList,
        semantic.typ
      ),
      Constructor.typingJustification(semantic)
    ) {

  printAs(args => renderAppliedSymbol(semantic.fullName, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.fullName
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val get_arity: Int = valueOfN.value
  val term: Expr[Ind] = termAt(typeVariablesSeq)

  def intro: THM = {
    requireMonomorphicAccess("constructor", name, typeVariablesSeq)
    theoremAt(name, typeVariablesSeq, Seq.empty, "introduction", semantic.intro)
  }

  def intro(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, firstTypeArg +: otherTypeArgs, "introduction", semantic.intro)

  def introApp: THM = {
    requireMonomorphicAccess("constructor", name, typeVariablesSeq)
    buildIntroAppAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = Seq.empty,
      baseTheorem = semantic.intro,
      headTermAt = termAt,
      headTypeAt = substitutions => semantic.typ.substitute(substitutions*),
      assumptionsAt = substitutions =>
        wellTypedSet(instantiatedSemanticSignature(semantic.semanticSignature, substitutions)),
      typingArgsAt = substitutions =>
        instantiatedSemanticSignature(semantic.semanticSignature, substitutions),
      conclusionAt = substitutions =>
        semantic.appliedTerm.substitute(substitutions*) ::
          semantic.adt.term.substitute(substitutions*)
    )
  }

  def introApp(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM = buildIntroAppAt(
    displayName = name,
    typeVariables = typeVariablesSeq,
    typeArgs = firstTypeArg +: otherTypeArgs,
    baseTheorem = semantic.intro,
    headTermAt = termAt,
    headTypeAt = substitutions => semantic.typ.substitute(substitutions*),
    assumptionsAt = substitutions =>
      wellTypedSet(instantiatedSemanticSignature(semantic.semanticSignature, substitutions)),
    typingArgsAt = substitutions =>
      instantiatedSemanticSignature(semantic.semanticSignature, substitutions),
    conclusionAt = substitutions =>
      semantic.appliedTerm.substitute(substitutions*) ::
        semantic.adt.term.substitute(substitutions*)
  )

  def injectivity: THM = {
    requireMonomorphicAccess("constructor", name, typeVariablesSeq)
    theoremAt(name, typeVariablesSeq, Seq.empty, "injectivity", semantic.injectivity)
  }

  def injectivity(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, firstTypeArg +: otherTypeArgs, "injectivity", semantic.injectivity)

  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] =
    (this #@@ args).asInstanceOf[Expr[Ind]]

  def applyUnsafe(args: Expr[Ind] ** N): Expr[Ind] = termAt(args.toSeq)

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)
}

object Constructor {
  private def typingJustification[N <: Arity](using
      line: sourcecode.Line,
      file: sourcecode.File
  )(semantic: SemanticConstructor[N]): THM =
    theoremAt(
      displayName = semantic.fullName,
      typeVariables = semantic.typeVariablesSeq,
      typeArgs = Seq.empty,
      suffix = "introduction",
      baseTheorem = semantic.intro
    )
}
