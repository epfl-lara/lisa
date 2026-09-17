package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.FunctionSemanticsBase
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax.Case
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.requireMonomorphicAccess
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.theoremAt
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.introAppAt
import lisa.maths.SetTheory.Types.ADTv2.support.core.**
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.core.toSeq
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.FunctionalClass
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Interface-level wrapper around the semantic layer of a (possibly recursive)
 * function defined by pattern matching.
 *
 * The whole user-facing surface (`intro`, `introApp`, the `elim*` family,
 * application) is identical for the non-recursive ([[ADTFunction]]) and
 * recursive ([[RecFunction]]) cases; only the diagnostic wording and the name
 * of the freshly introduced application variable differ, supplied here through
 * [[kindLabel]] and [[introAppVariable]].
 */
abstract class AbstractFunction[N <: Arity](using
    val line: sourcecode.Line,
    val file: sourcecode.File,
    valueOfN: ValueOf[N]
)(
    val semantic: FunctionSemanticsBase[N],
    val adt: ADT[N]
) extends TypedConstantFunctional[IndOf[N]](
      semantic.id,
      FunctionalClass(
        List.fill(semantic.typeVariablesSeq.size)(None),
        semantic.typeVariablesSeq.toList,
        semantic.typ
      ),
      AbstractFunction.typingJustification(semantic)
    ) {

  /**
   * Human-readable kind used in diagnostics, e.g. "function" or "recursive function".
   */
  protected def kindLabel: String

  /**
   * Fresh variable standing for the argument in `introApp`.
   */
  protected def introAppVariable: Variable[Ind]

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
      throw new IllegalArgumentException(s"Pattern ${pattern.name} does not belong to $kindLabel $name.")
    )
    s"elimination/${pattern.name}/$index"
  }

  def intro: THM = {
    requireMonomorphicAccess(kindLabel, name, typeVariablesSeq)
    theoremAt(name, typeVariablesSeq, Seq.empty, "introduction", semantic.intro)
  }

  def intro(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, firstTypeArg +: otherTypeArgs, "introduction", semantic.intro)

  def introApp: THM = {
    requireMonomorphicAccess(kindLabel, name, typeVariablesSeq)
    introAppAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = Seq.empty,
      baseTheorem = semantic.intro,
      headTermAt = termAt,
      headTypeAt = substitutions => semantic.typ.substitute(substitutions*),
      assumptionsAt = substitutions => Set(introAppVariable :: semantic.argType.substitute(substitutions*)),
      typingArgsAt = substitutions => Seq(introAppVariable -> semantic.argType.substitute(substitutions*)),
      conclusionAt = substitutions =>
        app(termAt(typeVariablesSeq))(introAppVariable) ::
          semantic.returnType.substitute(substitutions*)
    )
  }

  def introApp(firstTypeArg: Expr[Ind], otherTypeArgs: Expr[Ind]*): THM = {
    val typeArgs = firstTypeArg +: otherTypeArgs
    introAppAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = typeArgs,
      baseTheorem = semantic.intro,
      headTermAt = termAt,
      headTypeAt = substitutions => semantic.typ.substitute(substitutions*),
      assumptionsAt = substitutions => Set(introAppVariable :: semantic.argType.substitute(substitutions*)),
      typingArgsAt = substitutions => Seq(introAppVariable -> semantic.argType.substitute(substitutions*)),
      conclusionAt = substitutions =>
        app(termAt(typeArgs))(introAppVariable) ::
          semantic.returnType.substitute(substitutions*)
    )
  }

  def elimByPattern(pattern: Pattern[N]): THM = {
    requireMonomorphicAccess(kindLabel, name, typeVariablesSeq)
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
    requireMonomorphicAccess(kindLabel, name, typeVariablesSeq)
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
    requireMonomorphicAccess(kindLabel, name, typeVariablesSeq)
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

object AbstractFunction {
  private def typingJustification[N <: Arity](using
      line: sourcecode.Line,
      file: sourcecode.File
  )(semantic: FunctionSemanticsBase[N]): THM =
    theoremAt(
      displayName = semantic.name,
      typeVariables = semantic.typeVariablesSeq,
      typeArgs = Seq.empty,
      suffix = "introduction",
      baseTheorem = semantic.intro
    )
}
