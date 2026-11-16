package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.FunctionSemanticsBase
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax.Case
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.generalTheorem

import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.introAppTheorem
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.FunctionalClass
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional

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
abstract class AbstractFunction[S](using
    val line: sourcecode.Line,
    val file: sourcecode.File,
    sort: Sort[S]
)(
    val semantic: FunctionSemanticsBase,
    val adt: ADT[?]
) extends TypedConstantFunctional[S](
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
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val term: Expr[Ind] = termAt(typeVariablesSeq)

  lazy val argType: Expr[Ind] = semantic.argType
  lazy val returnType: Expr[Ind] = semantic.returnType
  lazy val functionType: Expr[Ind] = semantic.typ
  private lazy val patterns: Seq[Pattern] = semantic.patterns

  private lazy val patternIndices: Map[Pattern, Int] =
    patterns.zipWithIndex.toMap

  private def eliminationSuffix(pattern: Pattern): String = {
    val index = patternIndices.getOrElse(
      pattern,
      throw new IllegalArgumentException(s"Pattern ${pattern.name} does not belong to $kindLabel $name.")
    )
    s"elimination/${pattern.name}/$index"
  }

  /**
   * Typing of the defined symbol, closed over the type variables. Instantiate at type
   * arguments with `of`, e.g. `length.intro of nat`.
   *
   * Reuses the theorem handed to [[TypedConstantFunctional]] as this symbol.s typing
   * justification rather than proving a second copy; `Typecheck` needs that
   * justification universally closed, so the two must not drift apart.
   */
  lazy val intro: THM = justif.asInstanceOf[THM]

  /**
   * The applied form of [[intro]]. A derived statement rather than an instance, so it is
   * proved once over the type variables; instantiate with `of (A := nat)`.
   */
  lazy val introApp: THM = introAppTheorem(
    displayName = name,
    baseTheorem = semantic.intro,
    headTerm = termAt(typeVariablesSeq),
    headType = semantic.typ,
    assumptions = Set(introAppVariable :: semantic.argType),
    typingArgs = Seq(introAppVariable -> semantic.argType),
    conclusion = app(termAt(typeVariablesSeq))(introAppVariable) :: semantic.returnType
  )

  /**
   * The defining equation of every branch at once. Instantiate with `of`.
   */
  lazy val elimTotal: THM =
    generalTheorem(name, typeVariablesSeq, "eliminationTotal", semantic.elimTotal)

  private lazy val elimByPatternThms: Map[Pattern, THM] =
    patterns.map(p => p -> generalTheorem(name, typeVariablesSeq, eliminationSuffix(p), semantic.elimByPattern(p))).toMap

  private lazy val elimByConstThms: Map[Constructor[?], THM] =
    adt.constructors
      .map(c => c -> generalTheorem(name, typeVariablesSeq, s"elimination/${c.semantic.name}", semantic.elimByConst(c.semantic)))
      .toMap

  /**
   * The defining equation of one branch. Instantiate with `of`.
   */
  def elimByPattern(pattern: Pattern): THM =
    elimByPatternThms.getOrElse(
      pattern,
      throw new IllegalArgumentException(s"Pattern ${pattern.name} does not belong to $kindLabel $name.")
    )

  /**
   * The defining equations of every branch covering one constructor. Instantiate with `of`.
   */
  def elimByConst(constructor: Constructor[?]): THM =
    elimByConstThms.getOrElse(
      constructor,
      throw new IllegalArgumentException(s"${constructor.name} is not a constructor of $kindLabel $name's domain.")
    )

  def elim: THM = elimTotal

  def elim(pattern: Pattern): THM = elimByPattern(pattern)

  def elim(constructor: Constructor[?]): THM = elimByConst(constructor)

  def elim(c: Case): THM = elimByPattern(patternFor(c))

  /**
   * Order- and binder-name-independent lookup of the branch matching `c`.
   *
   * The case is matched against the registered patterns by constructor identity
   * plus its concrete (guard) arguments, so it does not depend on the order in
   * which the branches were declared.
   */
  def patternFor(c: Case): Pattern =
    patterns
      .collectFirst { case p if p.matchesConstructorCase(c.cons.semantic, c.args) => p }
      .getOrElse(
        throw new IllegalArgumentException(
          s"No branch of $name matches case ${c.cons.name}(${c.args.mkString(", ")})."
        )
      )

  /** Applies exactly the declared type arguments and returns the set-theoretic function. */
  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] =
    require(args.size == typeVariablesSeq.size, s"Function $name expects ${typeVariablesSeq.size} type argument(s), got ${args.size}.")
    (this #@@ args).asInstanceOf[Expr[Ind]]

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)
}

object AbstractFunction {
  private def typingJustification(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(semantic: FunctionSemanticsBase): THM =
    generalTheorem(semantic.name, semantic.typeVariablesSeq, "introduction", semantic.intro)
}
