package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.{**, toSeq}
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.{FunctionalClass, TypedConstantFunctional}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{instantiatedSemanticSignature, introAppAt as buildIntroAppAt, theoremAt}
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.{renderAppliedSymbol, wellTypedSet}
import lisa.utils.prooflib.ProofTacticLib.Arity

final class Constructor[N <: Arity](using val line: sourcecode.Line, val file: sourcecode.File, valueOfN: ValueOf[N])(
    val semantic: SemanticConstructor[N]
) extends TypedConstantFunctional[Ind](
      semantic.id,
      FunctionalClass(Nil, Nil, semantic.typ),
      semantic.intro
    ) {

  printAs(args => renderAppliedSymbol(semantic.fullName, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.fullName
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val get_arity: Int = valueOfN.value
  val term: Expr[Ind] = termAt(typeVariablesSeq)

  lazy val intro: THM = theoremAt(
    displayName = name,
    typeVariables = typeVariablesSeq,
    typeArgs = Seq.empty,
    suffix = "introduction",
    baseTheorem = semantic.intro
  )

  lazy val introApp: THM = introAppAt()

  lazy val injectivity: THM = theoremAt(
    displayName = name,
    typeVariables = typeVariablesSeq,
    typeArgs = Seq.empty,
    suffix = "injectivity",
    baseTheorem = semantic.injectivity
  )

  def introAt(typeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, typeArgs, "introduction", semantic.intro)

  def introAppAt(typeArgs: Expr[Ind]*): THM = buildIntroAppAt(
    displayName = name,
    typeVariables = typeVariablesSeq,
    typeArgs = typeArgs,
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

  def injectivityAt(typeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, typeArgs, "injectivity", semantic.injectivity)

  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] = semantic.term(args)

  def applyUnsafe(args: Expr[Ind] ** N): Expr[Ind] = termAt(args.toSeq)

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)
}
