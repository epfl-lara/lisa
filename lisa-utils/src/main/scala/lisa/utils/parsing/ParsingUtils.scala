package lisa.utils.parsing

import lisa.utils.parsing.ParserException
import scallion.*
import scallion.util.Unfolds.unfoldLeft

trait ParsingUtils extends Operators { self: Parsers =>
  case class PrecedenceLevel[Op](operator: Syntax[Op], associativity: lisa.utils.parsing.Associativity)

  implicit class PrecedenceLevelDecorator[Op](operator: Syntax[Op]) {

    /**
     * Indicates the associativity of the operator.
     */
    infix def has(associativity: lisa.utils.parsing.Associativity): PrecedenceLevel[Op] = PrecedenceLevel(operator, associativity)
  }

  def singleInfix[Op, A](elem: Syntax[A], op: Syntax[Op])(function: (A, Op, A) => A, inverse: PartialFunction[A, (A, Op, A)] = PartialFunction.empty): Syntax[A] =
    (elem ~ opt(op ~ elem)).map(
      {
        case first ~ None => first
        case first ~ Some(op ~ second) => function(first, op, second)
      },
      v =>
        inverse.lift(v) match {
          // see the usage of singleInfix in infixOperators: the inverse function is the same for all ops, so it might
          // or might not be correct to unwrap the current element with the inverse function. Hence, provide both options.
          case Some(l, op, r) => Seq(l ~ Some(op ~ r), v ~ None)
          case None => Seq(v ~ None)
        }
    )

  def infixOperators[Op, A](elem: Syntax[A])(levels: PrecedenceLevel[Op]*)(function: (A, Op, A) => A, inverse: PartialFunction[A, (A, Op, A)] = PartialFunction.empty): Syntax[A] =
    levels.foldLeft(elem) { case (currSyntax, PrecedenceLevel(op, assoc)) =>
      assoc match {
        case Associativity.Left => infixLeft(currSyntax, op)(function, inverse)
        case Associativity.Right => infixRight(currSyntax, op)(function, inverse)
        case Associativity.None => singleInfix(currSyntax, op)(function, inverse)
      }
    }
}
