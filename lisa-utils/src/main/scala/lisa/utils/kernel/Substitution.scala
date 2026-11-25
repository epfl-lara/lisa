package lisa.utils.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.{proof => K}

/**
 * Derive assumed and lifted equality substitution from proof-backed substitution.
 */
object Substitution:
  type Result = Either[String, K.Thm]

  private def checked(result: Either[?, K.Thm]): Result = result.left.map(_.toString)

  private[utils] def freshArguments(source: Expression, target: Expression, avoid: Iterable[Variable] = Nil): Seq[Variable] =
    if source.sort.depth == 0 then Nil
    else
      val taken = source.freeVariables.iterator ++ target.freeVariables.iterator ++ avoid.iterator
      val first = taken.map(_.id.no).maxOption.getOrElse(0) + 1
      (first until first + source.sort.depth).map(i => Variable(Identifier("x", i), Ind))

  private def pointwise(source: Expression, target: Expression, arguments: Seq[Variable]): Expression =
    val left = arguments.foldLeft(source: Expression)(_(_))
    val right = arguments.foldLeft(target: Expression)(_(_))
    if left.sort == Prop then iff(left)(right) else equality(left)(right)

  /**
   * Lift first-order function equality to a universally quantified pointwise comparison.
   */
  def liftedEqualities(equalities: Seq[(Expression, Expression)]): Seq[Expression] =
    equalities.map: (source, target) =>
      val arguments = freshArguments(source, target)
      arguments.foldRight(pointwise(source, target, arguments))((v, body) => forall(Lambda(v, body)))

  private[utils] def assumeComparison(assumption: Expression, replacement: (Expression, Expression, Seq[Variable]))(using K.Theory): Result =
    val (source, target, arguments) = replacement
    val equation = pointwise(source, target, arguments)
    if arguments.isEmpty then checked(K.Hypothesis(K.Sequent(Set(assumption), Set(equation)), equation))
    else
      val hypothesis = checked(K.Hypothesis(K.Sequent(Set(equation), Set(equation)), equation))
      arguments.zipWithIndex.foldRight(hypothesis):
        case ((argument, index), result) =>
          result.flatMap: current =>
            val body = current.left.head
            // Retain the supplied antecedent syntax at the outermost quantifier.
            val antecedent = if index == 0 then assumption else forall(Lambda(argument, body))
            checked(K.LeftForall(K.Sequent(Set(antecedent), Set(equation)), current, body, argument, argument))

  private def transport(
      statement: K.Sequent,
      premise: K.Thm,
      comparisons: Seq[K.Thm],
      replacements: Seq[(Expression, Expression, Seq[Variable])],
      context: (Seq[Variable], Expression),
      onLeft: Boolean
  )(using K.Theory): Result =
    if onLeft then checked(K.LeftSubst(statement, premise, comparisons, replacements, context))
    else checked(K.RightSubst(statement, premise, comparisons, replacements, context))

  /**
   * Use an equality proof directly, or discharge its lifted equality after substitution.
   */
  def withProof(
      statement: K.Sequent,
      premise: K.Thm,
      comparison: K.Thm,
      replacement: (Expression, Expression),
      context: (Variable, Expression),
      onLeft: Boolean
  )(using K.Theory): Result =
    val (source, target) = replacement
    if source.sort != target.sort || source.sort != context._1.sort || (!source.sort.isFunctional && !source.sort.isPredicate) then
      Left("Substitution sorts must match a first-order function or predicate sort.")
    else
      val equation = liftedEqualities(Seq(replacement)).head
      val variables = Seq(context._1) -> context._2
      if source.sort.depth == 0 && comparison.right.contains(equation) then transport(statement, premise, Seq(comparison), Seq((source, target, Nil)), variables, onLeft)
      else if comparison.right.size != 1 then Left("Expected exactly one lifted comparison on the right.")
      else
        for
          assumed <- simultaneous(K.Sequent(statement.left + equation, statement.right), premise, Seq(replacement), variables, onLeft)
          result <- checked(K.Cut(statement, comparison, assumed, equation))
        yield result

  /**
   * Assume lifted equalities and preserve simultaneous replacement semantics.
   */
  def simultaneous(
      statement: K.Sequent,
      premise: K.Thm,
      equalities: Seq[(Expression, Expression)],
      context: (Seq[Variable], Expression),
      onLeft: Boolean
  )(using K.Theory): Result =
    val (parameters, body) = context
    if body.sort != Prop then Left("Substitution context must be a formula.")
    else if parameters.size != equalities.size then Left("Substitution equality count must match the context's parameter count.")
    else if parameters.zip(equalities).exists { case (v, (s, t)) =>
        s.sort != v.sort || t.sort != v.sort || (!v.sort.isFunctional && !v.sort.isPredicate)
      }
    then Left("Substitution replacement sorts must match first-order context parameters.")
    else if parameters.isEmpty then
      val to = if onLeft then statement.left else statement.right
      if to.contains(body) || to.exists(isSame(_, body)) then checked(K.Weakening(statement, premise))
      else Left("Substitution conclusion is missing the substituted formula.")
    else
      val assumptions = liftedEqualities(equalities).map(e => statement.left.find(_ == e).orElse(statement.left.find(isSame(_, e))))
      if assumptions.exists(_.isEmpty) then Left("Substitution conclusion is missing a lifted equality.")
      else
        val retained = assumptions.flatten
        val replacements = equalities
          .zip(retained)
          .map:
            case ((source, target), assumption) => (source, target, freshArguments(source, target, assumption.freeVariables))
        val comparisons = replacements
          .zip(retained)
          .foldLeft(Right(Vector.empty[K.Thm]): Either[String, Vector[K.Thm]]):
            case (result, (replacement, assumption)) =>
              for
                accumulated <- result
                comparison <- assumeComparison(assumption, replacement)
              yield accumulated :+ comparison
        comparisons.flatMap(proofs => transport(statement, premise, proofs, replacements, context, onLeft))
