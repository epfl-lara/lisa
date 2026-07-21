package lisa.utils.prooflib

import lisa.kernel.fol.{FOL => KF}
import lisa.kernel.proof.{Helpers => KH}
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
    KH.expEq(s.underlying, t.underlying)

  extension [S](set: Set[Expr[S]])
    /**
     * Checks whether this high-level expression set contains an equivalent formula.
     */
    inline def containsEq[T](formula: Expr[T]): Boolean =
      KH.containsEq(set.map(_.underlying))(formula.underlying)

    /**
     * Checks whether every expression in this set is equivalent to one in the target set.
     */
    inline def subsetOfEq[T](target: Set[Expr[T]]): Boolean =
      KH.subsetOfEq(set.map(_.underlying))(target.map(_.underlying))

    /**
     * Checks whether this set is contained in the target set, allowing one exceptional expression.
     */
    inline def containedExcept[T, U](target: Set[Expr[T]], exception: Expr[U]): Boolean =
      KH.containedExcept(set.map(_.underlying))(target.map(_.underlying), exception.underlying)

    /**
     * Checks whether this set is contained in the target set, allowing either of two exceptional expressions.
     */
    inline def containedExceptEither[T, U, V](target: Set[Expr[T]], exception1: Expr[U], exception2: Expr[V]): Boolean =
      KH.containedExceptEither(set.map(_.underlying))(target.map(_.underlying), exception1.underlying, exception2.underlying)

  /**
   * Returns source expressions that are not equivalent to any expression in the target set.
   */
  def differenceEq(source: Set[KF.Expression], target: Set[KF.Expression]): Iterator[KF.Expression] =
    source.iterator.filterNot(expr => KH.containsEq(target)(expr))

  /**
   * Keeps the first representative of each simple normal form, optionally confirming exact equality.
   */
  def distinctEq(expressions: Iterator[KF.Expression], limit: Int = Int.MaxValue, exact: Boolean = false): Vector[KF.Expression] =
    val seen = mutable.HashSet.empty[KF.SimpleExpression]
    val result = Vector.newBuilder[KF.Expression]
    val kept = mutable.ArrayBuffer.empty[KF.Expression]
    var size = 0
    while size < limit && expressions.hasNext do
      val expression = expressions.next()
      if seen.add(KF.simpleReducedForm(expression)) && (!exact || !kept.exists(KH.expEq(_, expression))) then
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
    def liftEquality(s: KF.Expression, t: KF.Expression): KF.Expression =
      val maxId = (s.freeVariables ++ t.freeVariables).map(_.id.no).maxOption.getOrElse(0) + 1
      val vars = (maxId until (maxId + s.sort.depth)).map(i => KF.Variable(KF.Identifier("x", i), KF.Ind))
      val sApplied = vars.foldLeft(s)((f, arg) => f(arg))
      val tApplied = vars.foldLeft(t)((f, arg) => f(arg))
      val base =
        if sApplied.sort == KF.Prop then KF.iff(sApplied)(tApplied)
        else KF.equality(sApplied)(tApplied)
      vars.foldRight(base) { case (arg, acc) => KF.forall(KF.Lambda(arg, acc)) }

    equalities.map(liftEquality)

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

  /**
   * Builds a common abstraction of source and target by replacing matching s/t differences with variable.
   */
  private def abstractDifference(source: KF.Expression, target: KF.Expression, s: KF.Expression, t: KF.Expression, variable: KF.Variable): Option[(KF.Expression, Boolean)] =
    if source.sort != target.sort then None
    else if source.sort == s.sort && target.sort == t.sort && KH.expEq(source, s) && KH.expEq(target, t) then Some(variable -> true)
    else if KH.expEq(source, target) then Some(source -> false)
    else
      (source, target) match
        case (KF.Application(sourceF, sourceArg), KF.Application(targetF, targetArg)) =>
          for
            (newF, changedF) <- abstractDifference(sourceF, targetF, s, t, variable)
            (newArg, changedArg) <- abstractDifference(sourceArg, targetArg, s, t, variable)
          yield KF.Application(newF, newArg) -> (changedF || changedArg)
        case (KF.Lambda(sourceV, sourceBody), KF.Lambda(targetV, targetBody)) if sourceV == targetV =>
          abstractDifference(sourceBody, targetBody, s, t, variable).map { case (body, changed) =>
            KF.Lambda(sourceV, body) -> changed
          }
        case _ => None

  /**
   * Finds a one-variable formula abstraction whose substitution by s and t yields source and target.
   */
  def abstractReplacement(source: KF.Expression, target: KF.Expression, s: KF.Expression, t: KF.Expression): Option[(Seq[KF.Variable], KF.Expression)] =
    if source.sort != KF.Prop || target.sort != KF.Prop || s.sort != t.sort then None
    else
      val maxId = (source.freeVariables ++ target.freeVariables ++ s.freeVariables ++ t.freeVariables).map(_.id.no).maxOption.getOrElse(0) + 1
      val variable = KF.Variable(KF.Identifier("subst", maxId), s.sort)
      abstractDifference(source, target, s, t, variable).flatMap { case (body, changed) =>
        if !changed then None
        else
          val sourceCheck = KF.substituteVariables(body, Map(variable -> s))
          val targetCheck = KF.substituteVariables(body, Map(variable -> t))
          if KH.expEq(sourceCheck, source) && KH.expEq(targetCheck, target) then Some(Seq(variable) -> body)
          else None
      }

  /**
   * Enumerates single-substitution equality candidates from source/target formulas and available equalities.
   */
  def singleSubstEqCandidates(
      sourceFormulas: Iterator[KF.Expression],
      targetFormulas: Iterator[KF.Expression],
      equalityFormulas: Iterable[KF.Expression]
  ): Iterator[(Seq[(KF.Expression, KF.Expression)], (Seq[KF.Variable], KF.Expression))] =
    val sources = distinctEq(sourceFormulas).filter(_.sort == KF.Prop)
    val targets = distinctEq(targetFormulas).filter(_.sort == KF.Prop)
    val equalities = equalityFormulas.iterator
      .flatMap(unliftEquality)
      .flatMap { case (s, t) =>
        Iterator(s -> t, t -> s)
      }
      .toVector

    sources.iterator.flatMap { source =>
      targets.iterator.flatMap { target =>
        equalities.iterator.flatMap { case (s, t) =>
          abstractReplacement(source, target, s, t).map(lambdaPhi => Seq(s -> t) -> lambdaPhi)
        }
      }
    }
