package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax.Case
import lisa.maths.SetTheory.Types.ADTv2.recursion.RecFunSemantics
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.requireMonomorphicAccess
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.theoremAt
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{introAppAt => buildIntroAppAt}
import lisa.maths.SetTheory.Types.ADTv2.support.core.**
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.core.toSeq
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.FunctionalClass
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional
import lisa.utils.prooflib.ProofTacticLib.Arity

final class RecFunction[N <: Arity](using val line: sourcecode.Line, val file: sourcecode.File, valueOfN: ValueOf[N])(
    val semantic: RecFunSemantics[N],
    val adt: ADT[N]
) extends TypedConstantFunctional[IndOf[N]](
      semantic.id,
      FunctionalClass(
        List.fill(semantic.typeVariablesSeq.size)(None),
        semantic.typeVariablesSeq.toList,
        semantic.typ
      ),
      RecFunction.typingJustification(semantic)
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
  private lazy val patterns: Seq[Pattern[N]] = semantic.patterns

  private lazy val patternIndices: Map[Pattern[N], Int] =
    patterns.zipWithIndex.toMap

  private def eliminationSuffix(pattern: Pattern[N]): String = {
    val index = patternIndices.getOrElse(
      pattern,
      throw new IllegalArgumentException(s"Pattern ${pattern.name} does not belong to recursive function $name.")
    )
    s"elimination/${pattern.name}/$index"
  }

  def intro: THM = {
    requireMonomorphicAccess("recursive function", name, typeVariablesSeq)
    theoremAt(name, typeVariablesSeq, Seq.empty, "introduction", semantic.intro)
  }

  def intro(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, firstTypeArg +: otherTypeArgs, "introduction", semantic.intro)

  def introApp: THM = {
    requireMonomorphicAccess("recursive function", name, typeVariablesSeq)
    buildIntroAppAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = Seq.empty,
      baseTheorem = semantic.intro,
      headTermAt = termAt,
      headTypeAt = substitutions => semantic.typ.substitute(substitutions*),
      assumptionsAt = substitutions =>
        Set(RecFunction.introAppVariable :: semantic.argType.substitute(substitutions*)),
      typingArgsAt = substitutions =>
        Seq(RecFunction.introAppVariable -> semantic.argType.substitute(substitutions*)),
      conclusionAt = substitutions =>
        app(termAt(typeVariablesSeq))(RecFunction.introAppVariable) ::
          semantic.returnType.substitute(substitutions*)
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
        Set(RecFunction.introAppVariable :: semantic.argType.substitute(substitutions*)),
      typingArgsAt = substitutions =>
        Seq(RecFunction.introAppVariable -> semantic.argType.substitute(substitutions*)),
      conclusionAt = substitutions =>
        app(termAt(typeArgs))(RecFunction.introAppVariable) ::
          semantic.returnType.substitute(substitutions*)
    )
  }

  def elimByPattern(pattern: Pattern[N]): THM = {
    requireMonomorphicAccess("recursive function", name, typeVariablesSeq)
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = Seq.empty,
      suffix = eliminationSuffix(pattern),
      baseTheorem = semantic.elimByPattern(pattern)
    )
  }

  def elimByPattern(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*)(pattern: Pattern[N]): THM = {
    val typeArgs = firstTypeArg +: otherTypeArgs
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = typeArgs,
      suffix = eliminationSuffix(pattern),
      baseTheorem = semantic.elimByPattern(pattern)
    )
  }

  def elimByConst(constructor: Constructor[N]): THM = {
    requireMonomorphicAccess("recursive function", name, typeVariablesSeq)
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = Seq.empty,
      suffix = s"elimination/${constructor.semantic.name}",
      baseTheorem = semantic.elimByConst(constructor.semantic)
    )
  }

  def elimByConst(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*)(constructor: Constructor[N]): THM = {
    val typeArgs = firstTypeArg +: otherTypeArgs
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = typeArgs,
      suffix = s"elimination/${constructor.semantic.name}",
      baseTheorem = semantic.elimByConst(constructor.semantic)
    )
  }

  def elimTotal: THM = {
    requireMonomorphicAccess("recursive function", name, typeVariablesSeq)
    theoremAt(name, typeVariablesSeq, Seq.empty, "eliminationTotal", semantic.elimTotal)
  }

  def elimTotal(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, firstTypeArg +: otherTypeArgs, "eliminationTotal", semantic.elimTotal)


  def elim(): THM =
    elimTotal

  def elim(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM =
    elimTotal(firstTypeArg, otherTypeArgs*)

  def elim(pattern: Pattern[N]): THM =
    elimByPattern(pattern)

  def elim(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*)(pattern: Pattern[N]): THM =
    elimByPattern(firstTypeArg, otherTypeArgs*)(pattern)

  def elim(constructor: Constructor[N]): THM =
    elimByConst(constructor)

  def elim(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*)(constructor: Constructor[N]): THM =
    elimByConst(firstTypeArg, otherTypeArgs*)(constructor)

  def elim(c: Case[N]): THM =
    elimByPattern(patternFor(c))

  def elim(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*)(c: Case[N]): THM =
    elimByPattern(firstTypeArg, otherTypeArgs*)(patternFor(c))

  /**
   * Order- and binder-name-independent lookup of the branch matching `c`.
   *
   * The case is matched against the registered patterns by constructor identity
   * plus its concrete (guard) arguments, so it does not depend on the order in
   * which the branches were declared.
   */
  def patternFor(c: Case[N]): Pattern[N] =
    patterns
      .collectFirst { case p if p.matchesConstructorCase(c.cons.semantic, c.args) => p }
      .getOrElse(
        throw new IllegalArgumentException(
          s"No branch of $name matches case ${c.cons.name}(${c.args.mkString(", ")})."
        )
      )


  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] =
    (this #@@ args).asInstanceOf[Expr[Ind]]

  def applyUnsafe(args: Expr[Ind] ** N): Expr[Ind] = termAt(args.toSeq)

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)
}

object RecFunction {
  def selfReferenceName(functionName: String): String = s"${functionName}RecSelf"

  def selfPlaceholder(functionName: String): Variable[Ind] =
    Variable[Ind](selfReferenceName(functionName))

  private[ADTv2] val introAppVariable: Variable[Ind] =
    Variable[Ind]("recFunctionArg")

  private def typingJustification[N <: Arity](using
      line: sourcecode.Line,
      file: sourcecode.File
  )(semantic: RecFunSemantics[N]): THM =
    theoremAt(
      displayName = semantic.name,
      typeVariables = semantic.typeVariablesSeq,
      typeArgs = Seq.empty,
      suffix = "introduction",
      baseTheorem = semantic.intro
    )
}
