package lisa.kernel.proof

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus._

import scala.collection.mutable.ArrayBuffer

/** Instantiate lifted comparisons for proof-backed simultaneous substitution. */
object Substitution {
  /** Recover the heads compared by an equality, possibly under universal quantifiers. */
  def unliftEquality(formula: Expression): Option[(Expression, Expression)] = {
    def head(expression: Expression, arguments: List[Variable]): Option[Expression] = arguments match {
      case Nil => Some(expression)
      case argument :: rest => expression match {
        case Application(function, actual) if actual == argument => head(function, rest)
        case _ => None
      }
    }
    def loop(expression: Expression, arguments: List[Variable]): Option[(Expression, Expression)] = expression match {
      case forall(Lambda(v, body)) => loop(body, v :: arguments)
      case equality(s, t) => for (source <- head(s, arguments); target <- head(t, arguments)) yield source -> target
      case iff(s, t) => for (source <- head(s, arguments); target <- head(t, arguments)) yield source -> target
      case _ => None
    }
    loop(formula, Nil)
  }

  private def freshArguments(source: Expression, target: Expression, avoid: Iterable[Variable] = Nil): Seq[Variable] = {
    if (source.sort.depth == 0) Nil
    else {
      val taken = source.freeVariables.iterator ++ target.freeVariables.iterator ++ avoid.iterator
      val first = taken.map(_.id.no).maxOption.getOrElse(0) + 1
      (first until first + source.sort.depth).map(i => Variable(Identifier("x", i), Ind))
    }
  }

  private def pointwise(source: Expression, target: Expression, arguments: Seq[Variable]): Expression = {
    val left = arguments.foldLeft(source: Expression)(_(_))
    val right = arguments.foldLeft(target: Expression)(_(_))
    if (left.sort == Prop) iff(left)(right) else equality(left)(right)
  }

  /** Lift first-order function equality to a universally quantified pointwise comparison. */
  def liftedEqualities(equalities: Seq[(Expression, Expression)]): Seq[Expression] = equalities.map { case (source, target) =>
    val arguments = freshArguments(source, target)
    arguments.foldRight(pointwise(source, target, arguments))((v, body) => forall(Lambda(v, body)))
  }

  private class Builder {
    val steps = ArrayBuffer.empty[SCProofStep]
    def add(step: SCProofStep): Int = { steps += step; steps.size - 1 }

    def assumeComparison(assumption: Expression, replacement: (Expression, Expression, Seq[Variable])): Int = {
      val (source, target, arguments) = replacement
      val equation = pointwise(source, target, arguments)
      if (arguments.isEmpty) add(Hypothesis(Sequent(Set(assumption), Set(equation)), equation))
      else {
        val hypothesis = add(Hypothesis(Sequent(Set(equation), Set(equation)), equation))
        arguments.zipWithIndex.foldRight(hypothesis) { case ((argument, index), current) =>
          val body = steps(current).bot.left.head
          // Retain the supplied antecedent syntax at the outermost quantifier.
          val antecedent = if (index == 0) assumption else forall(Lambda(argument, body))
          add(LeftForall(Sequent(Set(antecedent), Set(equation)), current, body, argument, argument))
        }
      }
    }

    def transport(statement: Sequent, premise: Int, comparisons: Seq[Int], replacements: Seq[(Expression, Expression, Seq[Variable])], context: (Seq[Variable], Expression), onLeft: Boolean): Unit = {
      add(if (onLeft) LeftSubst(statement, premise, comparisons, replacements, context) else RightSubst(statement, premise, comparisons, replacements, context))
    }
  }

  /** Instantiate a lifted equality proof and transport one formula through it. */
  def withProof(statement: Sequent, premise: Sequent, comparison: Sequent, pair: (Expression, Expression), context: (Variable, Expression), onLeft: Boolean): Either[String, SCProof] = {
    val (source, target) = pair
    if (source.sort != target.sort || source.sort != context._1.sort || (!source.sort.isFunctional && !source.sort.isPredicate))
      Left("Substitution sorts must match a first-order function or predicate sort.")
    else {
      val builder = new Builder
      val taken = comparison.left.flatMap(_.freeVariables) ++ comparison.right.flatMap(_.freeVariables)
      val arguments = freshArguments(source, target, taken)
      val equation = liftedEqualities(Seq(pair)).head
      if ((arguments.nonEmpty || !comparison.right.contains(equation)) && comparison.right.size != 1) Left("Expected one lifted comparison on the right.")
      else {
        val instantiated =
          if (arguments.isEmpty && comparison.right.contains(equation)) -2
          else {
            val formula = comparison.right.head
            val bridge = builder.assumeComparison(formula, (source, target, arguments))
            builder.add(Cut(Sequent(comparison.left, builder.steps(bridge).bot.right), -2, bridge, formula))
          }
        builder.transport(statement, -1, Seq(instantiated), Seq((source, target, arguments)), Seq(context._1) -> context._2, onLeft)
        Right(SCProof(builder.steps.toVector, Vector(premise, comparison)))
      }
    }
  }

  /** Preserve simultaneous replacement without rewriting terms inserted by earlier replacements. */
  def simultaneous(statement: Sequent, premise: Sequent, equalities: Seq[(Expression, Expression)], context: (Seq[Variable], Expression), onLeft: Boolean): Either[String, SCProof] = {
    val (parameters, body) = context
    if (body.sort != Prop || parameters.size != equalities.size) Left("Substitution requires a formula and one equality per parameter.")
    else if (parameters.zip(equalities).exists { case (v, (s, t)) => s.sort != v.sort || t.sort != v.sort || (!v.sort.isFunctional && !v.sort.isPredicate) })
      Left("Substitution sorts must match first-order context parameters.")
    else {
      val to = if (onLeft) statement.left else statement.right
      if (parameters.isEmpty) {
        if (to.contains(body) || to.exists(isSame(_, body))) Right(SCProof(Vector(Weakening(statement, -1)), Vector(premise)))
        else Left("Substitution conclusion is missing the substituted formula.")
      }
      else {
        val assumptions = liftedEqualities(equalities).map(e => statement.left.find(_ == e).orElse(statement.left.find(isSame(_, e))))
        if (assumptions.exists(_.isEmpty)) Left("Substitution conclusion is missing a lifted equality.")
        else {
          val builder = new Builder
          val prepared = equalities.zip(assumptions.flatten).map { case ((source, target), assumption) =>
            val replacement = (source, target, freshArguments(source, target, assumption.freeVariables))
            builder.assumeComparison(assumption, replacement) -> replacement
          }
          val (comparisons, replacements) = prepared.unzip
          builder.transport(statement, -1, comparisons, replacements, context, onLeft)
          Right(SCProof(builder.steps.toVector, Vector(premise)))
        }
      }
    }
  }
}
