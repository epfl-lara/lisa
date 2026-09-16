package lisa.hol.core

import fastparse.*
import fastparse.NoWhitespace.*

/** Parse HOL Light terms and types in ProofTrace export syntax. */
object Parser:
  private def whitespace[$: P]: P[Unit] = P(CharsWhileIn(" \t\r\n\f\u000b", 0))

  // Delimiters terminate identifiers; spaces and Unicode inside names are significant.
  private def identifier[$: P]: P[String] = P(CharsWhile(c => c != '(' && c != ')' && c != '[' && c != ']').!)

  def typ[$: P]: P[Type] = P(typeVariable | typeApplication)
  def term[$: P]: P[Term] = P(variable | constant | combination | abstraction)

  // Commit after each distinct prefix: the remaining input belongs to that constructor.
  def variable[$: P]: P[Variable] =
    P(whitespace ~ "v(" ~/ identifier ~ ")(" ~ typ ~ whitespace ~ ")").map((name, tpe) => Variable(name, tpe))
  def constant[$: P]: P[Constant] =
    P(whitespace ~ "c(" ~/ identifier ~ ")(" ~ typ ~ whitespace ~ ")").map((name, tpe) => Constant(name, tpe))
  def combination[$: P]: P[Combination] =
    P(whitespace ~ "C(" ~/ term ~ whitespace ~ ")(" ~ term ~ whitespace ~ ")").map((left, right) => Combination(left, right))
  def abstraction[$: P]: P[Abstraction] =
    P(whitespace ~ "A(" ~/ variable ~ whitespace ~ ")(" ~ term ~ whitespace ~ ")").map((variable, body) => Abstraction(variable, body))

  def typeVariable[$: P]: P[TypeVariable] =
    P(whitespace ~ "v[" ~/ identifier ~ "]").map(TypeVariable.apply)
  def typeApplication[$: P]: P[TypeApplication] =
    P(whitespace ~ "c[" ~/ identifier ~ "][" ~ typeArg.rep ~ whitespace ~ "]").map((name, args) => TypeApplication(name, args.toList))
  private def typeArg[$: P]: P[Type] = P(whitespace ~ "[" ~/ typ ~ whitespace ~ "]")

  /** Parse the complete input, allowing trailing whitespace but rejecting trailing tokens. */
  def parseAll[T](input: String, parser: P[?] => P[T]): Parsed[T] =
    fastparse.parse(input, context =>
      given P[?] = context
      P(parser(context) ~ whitespace ~ End)
    )
