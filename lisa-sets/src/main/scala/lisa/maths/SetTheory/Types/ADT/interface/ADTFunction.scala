package lisa.maths.SetTheory.Types.ADT.interface

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.PatternMatching.syntax.Case
import lisa.maths.SetTheory.Types.ADT.recursion.SemanticFunction
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.generalTheorem
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.introAppTheorem
import lisa.maths.SetTheory.Types.ADT.support.TypedADTConstant
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.FunctionalClass
import lisa.utils.prooflib.Thm

/**
 * A typed function with its typing theorem and pattern equations.
 */
final class ADTFunction[S](using
    val line: sourcecode.Line,
    val file: sourcecode.File,
    sort: (S) is Sort
)(
    val semantic: SemanticFunction,
    val adt: ADT[?]
) extends TypedADTConstant[S](
      semantic.id,
      FunctionalClass(
        List.fill(semantic.typeVariablesSeq.size)(None),
        semantic.typeVariablesSeq.toList,
        semantic.typ
      ),
      ADTFunction.typingJustification(semantic)
    ) {

  private val introAppVariable: Variable[Ind] =
    Variable[Ind](freshId(semantic.typeVariablesSeq :+ semantic.typ, "functionArg"))

  printAs(args => renderAppliedSymbol(semantic.name, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.name
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val term: Expr[Ind] = termAt(typeVariablesSeq)

  lazy val argType: Expr[Ind] = semantic.argType
  lazy val returnType: Expr[Ind] = semantic.returnType
  lazy val functionType: Expr[Ind] = semantic.typ
  private lazy val patterns: Seq[Clause[Expr[Ind]]] = semantic.clauses

  private lazy val patternIndices: Map[Clause[Expr[Ind]], Int] =
    patterns.zipWithIndex.toMap

  private def eliminationSuffix(pattern: Clause[Expr[Ind]]): String = {
    val index = patternIndices.getOrElse(
      pattern,
      throw new IllegalArgumentException(s"Pattern ${pattern.name} does not belong to function $name.")
    )
    s"elimination/${pattern.name}/$index"
  }

  /**
   * The applied form of [[intro]]. A derived statement rather than an instance, so it is
   * proved once over the type variables; instantiate with `of (A := nat)`.
   */
  lazy val introApp: Theorem = introAppTheorem(
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
  lazy val elimTotal: Theorem =
    generalTheorem(name, typeVariablesSeq, "eliminationTotal", semantic.elimTotal)

  private val elimByPatternThms = scala.collection.mutable.Map.empty[Clause[Expr[Ind]], Theorem]
  private val elimByConstThms = scala.collection.mutable.Map.empty[Constructor[?], Theorem]
  private lazy val patternsByConstructor = patterns.groupBy(_.semanticConstructor)

  /**
   * The defining equation of one branch. Instantiate with `of`.
   */
  def elimByPattern(pattern: Clause[Expr[Ind]]): Theorem =
    elimByPatternThms.getOrElseUpdate(
      pattern,
      generalTheorem(name, typeVariablesSeq, eliminationSuffix(pattern), semantic.elimByPattern(pattern))
    )

  /**
   * The defining equations of every branch covering one constructor. Instantiate with `of`.
   */
  def elimByConst(constructor: Constructor[?]): Theorem =
    elimByConstThms.getOrElseUpdate(
      constructor, {
        require(
          (constructor.adt eq adt) && adt.constructors.contains(constructor),
          s"${constructor.name} is not a constructor of function $name's domain."
        )
        patternsByConstructor(constructor.semantic) match
          case Seq(pattern) => elimByPattern(pattern)
          case _ => generalTheorem(name, typeVariablesSeq, s"elimination/${constructor.semantic.name}", semantic.elimByConst(constructor.semantic))
      }
    )

  def elim: Theorem = elimTotal

  def elim(pattern: Clause[Expr[Ind]]): Theorem = elimByPattern(pattern)

  def elim(constructor: Constructor[?]): Theorem = elimByConst(constructor)

  def elim(c: Case): Theorem = elimByPattern(patternFor(c))

  /**
   * Order- and binder-name-independent lookup of the branch matching `c`.
   *
   * The case is matched against the registered patterns by constructor identity
   * plus its concrete (guard) arguments, so it does not depend on the order in
   * which the branches were declared.
   */
  def patternFor(c: Case): Clause[Expr[Ind]] =
    patterns
      .collectFirst { case p if p.matchesConstructorCase(c.cons.semantic, c.args) => p }
      .getOrElse(
        throw new IllegalArgumentException(
          s"No branch of $name matches case ${c.cons.name}(${c.args.mkString(", ")})."
        )
      )

  /**
   * Applies exactly the declared type arguments and returns the set-theoretic function.
   */
  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] =
    require(args.size == typeVariablesSeq.size, s"Function $name expects ${typeVariablesSeq.size} type argument(s), got ${args.size}.")
    (this #@@ args).asInstanceOf[Expr[Ind]]

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)
}

object ADTFunction {
  private def typingJustification(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(semantic: SemanticFunction): Theorem =
    generalTheorem(semantic.name, semantic.typeVariablesSeq, "introduction", semantic.intro)
}

/**
 * The same function interface, retained for existing recursive-function annotations.
 */
type RecFunction[S] = ADTFunction[S]
