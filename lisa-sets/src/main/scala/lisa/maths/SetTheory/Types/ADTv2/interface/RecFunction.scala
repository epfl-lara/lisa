package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Types.TypingHelpers.{::, FunctionalClass, TypedConstantFunctional}
import lisa.maths.SetTheory.Types.ADTv2.support.{**, toSeq}
import lisa.maths.SetTheory.Types.ADTv2.recursion.RecFunSemantics
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{introAppAt as buildIntroAppAt, theoremAt}
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.renderAppliedSymbol
import lisa.utils.prooflib.ProofTacticLib.Arity

final class RecFunction[N <: Arity](using val line: sourcecode.Line, val file: sourcecode.File, valueOfN: ValueOf[N])(
    val semantic: RecFunSemantics[N],
    val adt: ADT[N]
) extends TypedConstantFunctional[Ind](
      semantic.id,
      FunctionalClass(Nil, Nil, semantic.typ),
      semantic.intro
    ) {

  printAs(args => renderAppliedSymbol(semantic.name, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.name
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val get_arity: Int = valueOfN.value
  val term: Expr[Ind] = termAt(typeVariablesSeq)

  lazy val argType: Expr[Ind] = semantic.argType
  lazy val returnType: Expr[Ind] = semantic.returnType
  lazy val functionType: Expr[Ind] = semantic.typ

  lazy val intro: THM = theoremAt(
    displayName = name,
    typeVariables = typeVariablesSeq,
    typeArgs = Seq.empty,
    suffix = "introduction",
    baseTheorem = semantic.intro
  )

  lazy val introApp: THM = introAppAt()

  lazy val elim: Map[Constructor[N], THM] =
    adt.constructors.map(c =>
      c -> theoremAt(
        displayName = name,
        typeVariables = typeVariablesSeq,
        typeArgs = Seq.empty,
        suffix = s"elimination/${c.semantic.name}",
        baseTheorem = semantic.shortDefinition(c.semantic)
      )
    ).toMap

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
      Set(RecFunction.introAppVariable :: semantic.argType.substitute(substitutions*)),
    typingArgsAt = substitutions =>
      Seq(RecFunction.introAppVariable -> semantic.argType.substitute(substitutions*)),
    conclusionAt = substitutions =>
      app(termAt(if typeArgs.isEmpty then typeVariablesSeq else typeArgs))(RecFunction.introAppVariable) ::
        semantic.returnType.substitute(substitutions*)
  )

  def elimAt(typeArgs: Expr[Ind]*): Map[Constructor[N], THM] =
    adt.constructors.map(c =>
      c -> theoremAt(
        displayName = name,
        typeVariables = typeVariablesSeq,
        typeArgs = typeArgs,
        suffix = s"elimination/${c.semantic.name}",
        baseTheorem = semantic.shortDefinition(c.semantic)
      )
    ).toMap

  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] = semantic.term(args)

  def applyUnsafe(args: Expr[Ind] ** N): Expr[Ind] = termAt(args.toSeq)

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)

  lazy val debug_uniqueness: THM = semantic.uniqueness
  lazy val debug_classDefinitionFact: THM = semantic.classDefinitionFact
}

object RecFunction {
  def selfReferenceName(functionName: String): String = s"${functionName}RecSelf"

  def selfPlaceholder(functionName: String): Variable[Ind] =
    Variable[Ind](selfReferenceName(functionName))

  private[ADTv2] val introAppVariable: Variable[Ind] =
    Variable[Ind]("recFunctionArg")
}
