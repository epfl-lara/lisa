package lisa.utils

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL._
import lisa.kernel.fol.FOL.equality
import lisa.kernel.proof.SequentCalculus.*
import scallion.*
import silex.*

object Parser {

  class ParserException(msg: String) extends Exception(msg)
  object UnreachableException extends ParserException("Internal error: expected unreachable")

  def parseSequent(s: String): Sequent =
    extractParseResult(SequentParser.parseSequent(SequentLexer(s.iterator)))

  def parseFormula(s: String): Formula =
    extractParseResult(SequentParser.parseFormula(SequentLexer(s.iterator)))

  def parseTerm(s: String): Term =
    extractParseResult(SequentParser.parseTerm(SequentLexer(s.iterator)))

  private def extractParseResult[T](r: SequentParser.ParseResult[T]): T = r match {
    case SequentParser.Parsed(value, _) => value
    // TODO: at position
    // TODO: leaking implementation? Should I sugar tokens? -- Lexer.unapply once it's implemented
    case SequentParser.UnexpectedToken(token, _) => throw ParserException(s"Unexpected input: $token")
    case SequentParser.UnexpectedEnd(_) => throw ParserException(s"Unexpected end of input")
  }

  private[Parser] sealed abstract class FormulaToken
  case object ForallToken extends FormulaToken
  case object ExistsOneToken extends FormulaToken
  case object ExistsToken extends FormulaToken
  case object DotToken extends FormulaToken
  case object AndToken extends FormulaToken
  case object OrToken extends FormulaToken
  case object ImpliesToken extends FormulaToken
  case object IffToken extends FormulaToken
  case object NegationToken extends FormulaToken
  case object EqualityToken extends FormulaToken
  // Constant functions and predicates
  case class ConstantToken(id: String) extends FormulaToken
  // Variables, schematic functions and predicates
  case class SchematicToken(id: String) extends FormulaToken
  case class ParenthesisToken(isOpen: Boolean) extends FormulaToken
  case object CommaToken extends FormulaToken
  case object SemicolonToken extends FormulaToken
  case object SequentToken extends FormulaToken
  case object SpaceToken extends FormulaToken

  private[Parser] object SequentLexer extends Lexers with CharLexers {
    type Token = FormulaToken
    // TODO: add positions ==> ranges to tokens
    type Position = Unit

    private val lexer = Lexer(
      elem('∀') |> { _ => ForallToken },
      word("∃!") |> { _ => ExistsOneToken },
      elem('∃') |> { _ => ExistsToken },
      elem('.') |> { _ => DotToken },
      elem('=') |> { _ => EqualityToken },
      elem('∧') | word("/\\") |> { _ => AndToken },
      elem('∨') | word("\\/") |> { _ => OrToken },
      elem('⇒') | word("=>") | word("==>") |> { _ => ImpliesToken },
      elem('↔') | word("<=>") | word("<==>") |> { _ => IffToken },
      elem('¬') | elem('!') |> { _ => NegationToken },
      elem('(') |> ParenthesisToken(true),
      elem(')') |> ParenthesisToken(false),
      elem(',') |> CommaToken,
      elem(';') |> SemicolonToken,
      elem('⊢') | word("|-") |> SequentToken,
      many1(whiteSpace) |> SpaceToken,
      elem('?') ~ many1(elem(_.isLetter) | elem('_') | elem(_.isDigit) | elem('\'')) |> { cs =>
        // drop the '?'
        SchematicToken(cs.drop(1).mkString)
      },
      many1(elem(_.isLetter) | elem('_') | elem(_.isDigit)) |> { cs => ConstantToken(cs.mkString) }
    ) onError { (cs, _) =>
      throw ParserException(s"Unexpected input: ${cs.mkString}")
    }

    def apply(it: Iterator[Char]): Iterator[Token] = {
      val source = Source.fromIterator(it, NoPositioner)
      lexer(source).filter(_ != SpaceToken)
    }
  }

  private[Parser] object SequentParser extends Parsers {
    sealed abstract class TokenKind
    // and, or are both (left) associative and bind tighter than implies, iff
    case object AndKind extends TokenKind
    case object OrKind extends TokenKind
    // implies, iff are both non-associative and are of equal priority, lower than and, or

    case object TopLevelConnectorKind extends TokenKind
    case object NegationKind extends TokenKind
    case object FunctionOrPredicateKind extends TokenKind
    case object EqualityKind extends TokenKind
    case object CommaKind extends TokenKind
    case class ParenthesisKind(isOpen: Boolean) extends TokenKind
    case object BinderKind extends TokenKind
    case object DotKind extends TokenKind
    case object SemicolonKind extends TokenKind
    case object SequentSymbolKind extends TokenKind
    case object OtherKind extends TokenKind

    type Token = lisa.utils.Parser.FormulaToken
    type Kind = TokenKind

    // can safely skip tokens which were mapped to unit with elem(kind).unit(token)
    import SafeImplicits._

    def getKind(t: Token): Kind = t match {
      case AndToken => AndKind
      case OrToken => OrKind
      case IffToken | ImpliesToken => TopLevelConnectorKind
      case NegationToken => NegationKind
      case _: ConstantToken | _: SchematicToken => FunctionOrPredicateKind
      case EqualityToken => EqualityKind
      case CommaToken => CommaKind
      case ParenthesisToken(isOpen) => ParenthesisKind(isOpen)
      case ExistsToken | ExistsOneToken | ForallToken => BinderKind
      case DotToken => DotKind
      case SemicolonToken => SemicolonKind
      case SequentToken => SequentSymbolKind
      case SpaceToken => OtherKind
    }

    /////////////////////// SEPARATORS ////////////////////////////////
    def parens(isOpen: Boolean): Syntax[Unit] =
      elem(ParenthesisKind(isOpen)).unit(ParenthesisToken(isOpen))

    val open: Syntax[Unit] = parens(true)

    val closed: Syntax[Unit] = parens(false)

    val comma: Syntax[Unit] = elem(CommaKind).unit(CommaToken)

    val eq: Syntax[Unit] = elem(EqualityKind).unit(EqualityToken)

    val semicolon: Syntax[Unit] = elem(SemicolonKind).unit(SemicolonToken)

    val sequentSymbol: Syntax[Unit] = elem(SequentSymbolKind).unit(SequentToken)
    ///////////////////////////////////////////////////////////////////

    //////////////////////// LABELS ///////////////////////////////////
    val toplevelConnector: Syntax[Implies.type | Iff.type] = accept(TopLevelConnectorKind) {
      case ImpliesToken => Implies
      case IffToken => Iff
    }

    val negation: Syntax[Neg.type] = accept(NegationKind) { case NegationToken => Neg }
    ///////////////////////////////////////////////////////////////////

    //////////////////////// TERMS ////////////////////////////////////
    lazy val args: Syntax[Seq[Term]] = recursive(open.skip ~ repsep(term, comma) ~ closed.skip)

    lazy val term: Syntax[Term] = recursive((elem(FunctionOrPredicateKind) ~ opt(args)).map {
      case ConstantToken(id) ~ maybeArgs =>
        val args = maybeArgs.getOrElse(Seq())
        FunctionTerm(ConstantFunctionLabel(id, args.length), args)
      case SchematicToken(id) ~ Some(args) => FunctionTerm(SchematicFunctionLabel(id, args.length), args)
      case SchematicToken(id) ~ None => VariableTerm(VariableLabel(id))
      case _ => throw UnreachableException
    })
    ///////////////////////////////////////////////////////////////////

    //////////////////////// FORMULAS /////////////////////////////////
    // can appear without parentheses
    lazy val simpleFormula: Syntax[Formula] = predicate.up[Formula] | negated.up[Formula]
    lazy val subformula: Syntax[Formula] = simpleFormula | open.skip ~ formula ~ closed.skip

    def createFunctionTerm(label: Token, args: Seq[Term]): Term = label match {
      case ConstantToken(id) => FunctionTerm(ConstantFunctionLabel(id, args.size), args)
      case SchematicToken(id) =>
        args match {
          case Seq() => VariableTerm(VariableLabel(id))
          case _ => FunctionTerm(SchematicFunctionLabel(id, args.size), args)
        }
      case _ => throw UnreachableException
    }

    val predicate: Syntax[PredicateFormula] = (elem(FunctionOrPredicateKind) ~ opt(args) ~ opt(eq.skip ~ elem(FunctionOrPredicateKind) ~ opt(args))).map {
      // predicate application
      case ConstantToken(id) ~ maybeArgs ~ None =>
        val args = maybeArgs.getOrElse(Seq())
        PredicateFormula(ConstantPredicateLabel(id, args.size), args)
      case SchematicToken(id) ~ Some(args) ~ None => PredicateFormula(SchematicNPredicateLabel(id, args.size), args)
      case SchematicToken(id) ~ None ~ None => PredicateFormula(VariableFormulaLabel(id), Seq())

      // equality of two function applications
      case fun1 ~ args1 ~ Some(fun2 ~ args2) =>
        PredicateFormula(FOL.equality, Seq(createFunctionTerm(fun1, args1.getOrElse(Seq())), createFunctionTerm(fun2, args2.getOrElse(Seq()))))

      case _ => throw UnreachableException
    }

    val negated: Syntax[ConnectorFormula] = recursive {
      (negation ~ subformula).map { case n ~ f =>
        ConnectorFormula(n, Seq(f))
      }
    }

    // 'and' has higher priority than 'or'
    val connectorFormula: Syntax[Formula] = operators(subformula)(
      elem(AndKind) map {
        case AndToken => And
        case _ => throw UnreachableException
      } is LeftAssociative,
      elem(OrKind) map {
        case OrToken => Or
        case _ => throw UnreachableException
      } is LeftAssociative
    )(
      { case (l, conn, r) =>
        ConnectorFormula(conn, Seq(l, r))
      },
      { case ConnectorFormula(conn, Seq(l, r)) =>
        (l, conn, r)
      }
    )

    // consume binders and return a function that constructs a BinderFormula given the inner formula
    val binder: Syntax[(BinderLabel, VariableLabel)] = (accept(BinderKind) {
      case ExistsToken => Exists
      case ExistsOneToken => ExistsOne
      case ForallToken => Forall
    } ~ accept(FunctionOrPredicateKind) {
      case ConstantToken(id) => VariableLabel(id)
      case SchematicToken(id) => VariableLabel(id)
    } ~ elem(DotKind).unit(DotToken).skip) map { case b ~ v =>
      (b, v)
    }

    lazy val formula: Syntax[Formula] = recursive {
      (many(binder) ~ connectorFormula ~ opt(toplevelConnector ~ connectorFormula)) map { case binders ~ f ~ rest =>
        val inner = rest match {
          case Some(conn ~ f2) => ConnectorFormula(conn, Seq(f, f2))
          case None => f
        }
        binders.foldRight(inner) { case ((binder, v), f) =>
          BinderFormula(binder, v, f)
        }
      }
    }
    ///////////////////////////////////////////////////////////////////
    val sequent: Syntax[Sequent] = repsep(formula, semicolon) ~ opt(sequentSymbol.skip ~ repsep(formula, semicolon)) map {
      case left ~ Some(right) => Sequent(left.toSet, right.toSet)
      case right ~ None => Sequent(Set(), right.toSet)
    }

    val parser: Parser[Sequent] = Parser(sequent)

    val formulaParser: SequentParser.Parser[FOL.Formula] = Parser(formula)

    val termParser: SequentParser.Parser[FOL.Term] = Parser(term)

    def apply(it: Iterator[Token]): ParseResult[Sequent] = parseSequent(it)

    def parseSequent(it: Iterator[Token]): ParseResult[Sequent] = parser(it)

    def parseFormula(it: Iterator[Token]): ParseResult[Formula] = formulaParser(it)

    def parseTerm(it: Iterator[Token]): ParseResult[Term] = termParser(it)
  }
}
