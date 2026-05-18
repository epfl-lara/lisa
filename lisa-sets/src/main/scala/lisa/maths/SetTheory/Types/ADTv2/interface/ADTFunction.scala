package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Types.TypingHelpers.{::, FunctionalClass, TypedConstantFunctional}
import lisa.maths.SetTheory.Types.ADTv2.support.{**, toSeq}
import lisa.maths.SetTheory.Types.ADTv2.functions.SemanticFunction
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{introAppAt as buildIntroAppAt, requireMonomorphicAccess, theoremAt}
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.renderAppliedSymbol
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Type theoretic function over algebraic data types. Its definition is the direct sum of
 * the definitions of its constructors. Comes with introduction and elimination rules.
 */
final class ADTFunction[N <: Arity](using val line: sourcecode.Line, val file: sourcecode.File, valueOfN: ValueOf[N])(
    val semantic: SemanticFunction[N],
    val adt: ADT[N]
) extends TypedConstantFunctional[IndOf[N]](
      semantic.id,
      FunctionalClass(
        List.fill(semantic.typeVariablesSeq.size)(None),
        semantic.typeVariablesSeq.toList,
        semantic.typ
      ),
      ADTFunction.typingJustification(semantic)
    ) {

  printAs(args => renderAppliedSymbol(semantic.fullName, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.fullName
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val get_arity: Int = valueOfN.value
  val term: Expr[Ind] = termAt(typeVariablesSeq)

  lazy val argType: Expr[Ind] = semantic.adtDomain.term
  lazy val returnType: Expr[Ind] = semantic.returnTypeExpr
  lazy val functionType: Expr[Ind] = semantic.typ

  def intro: THM = {
    requireMonomorphicAccess("function", name, typeVariablesSeq)
    theoremAt(name, typeVariablesSeq, Seq.empty, "introduction", semantic.intro)
  }

  def intro(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, firstTypeArg +: otherTypeArgs, "introduction", semantic.intro)

  def introApp: THM = {
    requireMonomorphicAccess("function", name, typeVariablesSeq)
    buildIntroAppAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = Seq.empty,
      baseTheorem = semantic.intro,
      headTermAt = termAt,
      headTypeAt = substitutions => semantic.typ.substitute(substitutions*),
      assumptionsAt = substitutions =>
        Set(ADTFunction.introAppVariable :: semantic.adtDomain.term.substitute(substitutions*)),
      typingArgsAt = substitutions =>
        Seq(ADTFunction.introAppVariable -> semantic.adtDomain.term.substitute(substitutions*)),
      conclusionAt = substitutions =>
        app(termAt(typeVariablesSeq))(ADTFunction.introAppVariable) ::
          semantic.returnTypeExpr.substitute(substitutions*)
    )
  }

  def introApp(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM = {
    val typeArgs = firstTypeArg +: otherTypeArgs
    buildIntroAppAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = typeArgs,
      baseTheorem = semantic.intro,
      headTermAt = termAt,
      headTypeAt = substitutions => semantic.typ.substitute(substitutions*),
      assumptionsAt = substitutions =>
        Set(ADTFunction.introAppVariable :: semantic.adtDomain.term.substitute(substitutions*)),
      typingArgsAt = substitutions =>
        Seq(ADTFunction.introAppVariable -> semantic.adtDomain.term.substitute(substitutions*)),
      conclusionAt = substitutions =>
        app(termAt(typeArgs))(ADTFunction.introAppVariable) ::
          semantic.returnTypeExpr.substitute(substitutions*)
    )
  }

  def elim: Map[Constructor[N], THM] = {
    requireMonomorphicAccess("function", name, typeVariablesSeq)
    adt.constructors.map(c =>
      c -> theoremAt(
        displayName = name,
        typeVariables = typeVariablesSeq,
        typeArgs = Seq.empty,
        suffix = s"elimination/${c.semantic.name}",
        baseTheorem = semantic.shortDefinition(c.semantic)
      )
    ).toMap
  }

  def elim(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): Map[Constructor[N], THM] = {
    val typeArgs = firstTypeArg +: otherTypeArgs
    adt.constructors.map(c =>
      c -> theoremAt(
        displayName = name,
        typeVariables = typeVariablesSeq,
        typeArgs = typeArgs,
        suffix = s"elimination/${c.semantic.name}",
        baseTheorem = semantic.shortDefinition(c.semantic)
      )
    ).toMap
  }

  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] =
    (this #@@ args).asInstanceOf[Expr[Ind]]

  def applyUnsafe(args: Expr[Ind] ** N): Expr[Ind] = termAt(args.toSeq)

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)
}

object ADTFunction {
  private[ADTv2] val introAppVariable: Variable[Ind] =
    Variable[Ind]("functionArg")

  private def typingJustification[N <: Arity](using
      line: sourcecode.Line,
      file: sourcecode.File
  )(semantic: SemanticFunction[N]): THM =
    theoremAt(
      displayName = semantic.fullName,
      typeVariables = semantic.typeVariablesSeq,
      typeArgs = Seq.empty,
      suffix = "introduction",
      baseTheorem = semantic.intro
    )
}
