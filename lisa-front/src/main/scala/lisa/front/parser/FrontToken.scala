package lisa.front.parser

import scala.util.parsing.input.Positional

/**
 * Low-level tokens used by the lexer ([[FrontLexer]]).
 */
private[parser] enum FrontToken extends Positional {

  case Identifier(identifier: String)
  case SchematicIdentifier(identifier: String)
  case SchematicConnectorIdentifier(identifier: String)

  case IntegerLiteral(value: Int)

  case Indentation(spaces: Int)

  case NewLineWithIndentation(spaces: Int)
  case InitialIndentation(spaces: Int)

  // The reason these *must* be case classes is because they extend `Positional`,
  // which contains a position attribute (that shouldn't be shared between instances)

  case Turnstile()
  case And()
  case Or()
  case Implies()
  case Iff()
  case Equal()
  case Membership()
  case Subset()
  case SameCardinality()
  case Forall()
  case Exists()
  case ExistsOne()
  case Not()
  case EmptySet()
  case LocalBinder()

  case Ellipsis()

  case CurlyBracketOpen()
  case CurlyBracketClose()
  case SquareBracketOpen()
  case SquareBracketClose()
  case ParenthesisOpen()
  case ParenthesisClose()

  case Dot()
  case Comma()
  case Semicolon()

  case RuleName(name: String)

  case NewLine()

  case End()

}
