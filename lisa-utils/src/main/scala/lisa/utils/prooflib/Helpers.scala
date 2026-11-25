package lisa.utils.prooflib

import lisa.kernel.fol.{FOL => KF}
import lisa.utils.fol.FOL._

import scala.collection.mutable

object Helpers:

  ///////////////////////////////////////////////////////////////////////////////
  // Equality and set helpers
  ///////////////////////////////////////////////////////////////////////////////

  /**
   * Checks kernel expression equality for two high-level expressions.
   */
  inline def expEq[S, T](s: Expr[S], t: Expr[T]): Boolean =
    KF.isSame(s.underlying, t.underlying)

  extension [S](set: Set[Expr[S]])
    /**
     * Checks whether this high-level expression set contains an equivalent formula.
     */
    inline def containsEq[T](formula: Expr[T]): Boolean =
      KF.contains(set.map(_.underlying), formula.underlying)

    /**
     * Checks whether every expression in this set is equivalent to one in the target set.
     */
    inline def subsetOfEq[T](target: Set[Expr[T]]): Boolean =
      KF.isSubset(set.map(_.underlying), target.map(_.underlying))

    /**
     * Checks whether this set is contained in the target set, allowing one exceptional expression.
     */
    inline def containedExcept[T, U](target: Set[Expr[T]], exception: Expr[U]): Boolean =
      val underlyingTarget = target.map(_.underlying)
      set.forall(formula => KF.contains(underlyingTarget, formula.underlying) || expEq(formula, exception))

    /**
     * Checks whether this set is contained in the target set, allowing either of two exceptional expressions.
     */
    inline def containedExceptEither[T, U, V](target: Set[Expr[T]], exception1: Expr[U], exception2: Expr[V]): Boolean =
      val underlyingTarget = target.map(_.underlying)
      set.forall(formula => KF.contains(underlyingTarget, formula.underlying) || expEq(formula, exception1) || expEq(formula, exception2))

  /**
   * Returns source expressions that are not equivalent to any expression in the target set.
   */
  def differenceEq(source: Set[KF.Expression], target: Set[KF.Expression]): Iterator[KF.Expression] =
    source.iterator.filterNot(KF.contains(target, _))

  /**
   * Keeps the first representative of each simple normal form, optionally confirming exact equality.
   */
  def distinctEq(expressions: Iterator[KF.Expression], limit: Int = Int.MaxValue, exact: Boolean = false): Vector[KF.Expression] =
    val seen = mutable.HashSet.empty[KF.Expression]
    val result = Vector.newBuilder[KF.Expression]
    val kept = mutable.ArrayBuffer.empty[KF.Expression]
    var size = 0
    while size < limit && expressions.hasNext do
      val expression = expressions.next()
      if seen.add(KF.reducedForm(expression)) && (!exact || !kept.exists(KF.isSame(_, expression))) then
        result += expression
        kept += expression
        size += 1
    result.result()

  ///////////////////////////////////////////////////////////////////////////////
  // Printing helpers
  ///////////////////////////////////////////////////////////////////////////////

  /**
   * Format a base message with optional key-value parameters, each on a new line.
   */
  def withParams(base: String, params: (String, Any)*): String =
    if params.isEmpty then base
    else
      val paramStr = params.map((k, v) => s"\t$k: $v").mkString("\n")
      s"$base\n$paramStr"

  ///////////////////////////////////////////////////////////////////////////////
  // Term destruction and abstraction helpers
  ///////////////////////////////////////////////////////////////////////////////

  /**
   * Flattens a right/left-nested disjunction tree into its formula leaves.
   */
  def flattenOr(expression: KF.Expression): Vector[KF.Expression] =
    expression match
      case KF.or(left, right) => flattenOr(left) ++ flattenOr(right)
      case other => Vector(other)

  /**
   * Flattens a right/left-nested conjunction tree into its formula leaves.
   */
  def flattenAnd(expression: KF.Expression): Vector[KF.Expression] =
    expression match
      case KF.and(left, right) => flattenAnd(left) ++ flattenAnd(right)
      case other => Vector(other)

  /**
   * Iterates over expressions and their application/lambda subexpressions, outer nodes first.
   */
  def subexpressions(expressions: Iterable[KF.Expression]): Iterator[KF.Expression] =
    new Iterator[KF.Expression]:
      private val pending = mutable.ArrayDeque.from(expressions)

      def hasNext: Boolean = pending.nonEmpty

      def next(): KF.Expression =
        val expression = pending.removeHead()
        expression match
          case KF.Application(f, arg) =>
            pending.prepend(arg)
            pending.prepend(f)
          case KF.Lambda(variable, body) =>
            pending.prepend(body)
            pending.prepend(variable)
          case _ => ()
        expression

  /**
   * Returns distinct individual-sorted subterms appearing in the given expressions.
   */
  def termsIn(expressions: Iterable[KF.Expression]): Vector[KF.Expression] =
    distinctEq(subexpressions(expressions).filter(_.sort == KF.Ind))

  /**
   * Candidate instantiating terms for a quantified variable against a local formula instance.
   */
  def localTermCandidates(instance: KF.Expression, variable: KF.Variable): Iterator[KF.Expression] =
    Iterator.single(variable: KF.Expression) ++ termsIn(Seq(instance)).iterator

  /**
   * Converts equal function heads into universally quantified pointwise equalities.
   */
  def liftedEqualities(equalities: Seq[(KF.Expression, KF.Expression)]): Seq[KF.Expression] =
    lisa.utils.kernel.Substitution.liftedEqualities(equalities)

  /**
   * Splits a fully applied expression into its head and ordered argument list.
   */
  private def unfoldApplications(expression: KF.Expression): (KF.Expression, Vector[KF.Expression]) =
    def loop(current: KF.Expression, args: Vector[KF.Expression]): (KF.Expression, Vector[KF.Expression]) =
      current match
        case KF.Application(f, arg) => loop(f, arg +: args)
        case head => head -> args
    loop(expression, Vector.empty)

  /**
   * Removes leading universal quantifiers and returns their bound variables plus the body.
   */
  private def stripForalls(expression: KF.Expression): (Vector[KF.Variable], KF.Expression) =
    expression match
      case KF.forall(KF.Lambda(x: KF.Variable, body)) =>
        val (vars, inner) = stripForalls(body)
        (x +: vars) -> inner
      case other => Vector.empty -> other

  /**
   * Returns an application head exactly when the expression is applied to the given variables.
   */
  private def unappliedHead(expression: KF.Expression, args: Seq[KF.Variable]): Option[KF.Expression] =
    val (head, actualArgs) = unfoldApplications(expression)
    if actualArgs == args then Some(head) else None

  /**
   * Inverts a lifted equality or iff back to the two original equal heads when possible.
   */
  def unliftEquality(expression: KF.Expression): Option[(KF.Expression, KF.Expression)] =
    val (args, body) = stripForalls(expression)
    body match
      case KF.equality(left, right) =>
        if args.isEmpty then Some(left -> right)
        else
          for
            s <- unappliedHead(left, args)
            t <- unappliedHead(right, args)
          yield s -> t
      case KF.iff(left, right) =>
        if args.isEmpty then Some(left -> right)
        else
          for
            s <- unappliedHead(left, args)
            t <- unappliedHead(right, args)
          yield s -> t
      case _ => None
