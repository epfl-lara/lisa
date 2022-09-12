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

  def parseSequent(s: String): Sequent = s.split("⊢") match {
    case Array(fs) => Sequent(Set(), fs.split(";").map(parseFormula).toSet)
    case Array(fsl, fsr) => Sequent(fsl.split(";").map(parseFormula).toSet, fsr.split(";").map(parseFormula).toSet)
    case _ => throw ParserException("Invalid sequent")
  }

  private def extractParseResult[T](r: FormulaParser.ParseResult[T]): T = r match {
    case FormulaParser.Parsed(value, _) => value
    // TODO: at position
    // TODO: leaking implementation? Should I sugar tokens?
    case FormulaParser.UnexpectedToken(token, _) => throw ParserException(s"Unexpected input: $token")
    case FormulaParser.UnexpectedEnd(_) => throw ParserException(s"Unexpected end of input")
  }

  def parseFormula(s: String): Formula =
    extractParseResult(FormulaParser(FormulaLexer(s.iterator)))

  def parseTerm(s: String): Term =
    extractParseResult(FormulaParser.parseTerm(FormulaLexer(s.iterator)))

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
  case object SpaceToken extends FormulaToken

  private[Parser] object FormulaLexer extends Lexers with CharLexers {
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

  private[Parser] object FormulaParser extends Parsers {
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
      case SpaceToken => OtherKind
    }

    /////////////////////// SEPARATORS ////////////////////////////////
    def parens(isOpen: Boolean): Syntax[Unit] =
      elem(ParenthesisKind(isOpen)).unit(ParenthesisToken(isOpen))

    val open: Syntax[Unit] = parens(true)

    val closed: Syntax[Unit] = parens(false)

    val comma: Syntax[Unit] = elem(CommaKind).unit(CommaToken)

    val eq: Syntax[Unit] = elem(EqualityKind).unit(EqualityToken)
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

    def getBinderFormulaConstructor(binders: Seq[BinderLabel ~ VariableLabel]): Formula => Formula = binders match {
      case Seq() => f => f
      case (binder ~ boundVar) +: rest => f => BinderFormula(binder, boundVar, getBinderFormulaConstructor(rest)(f))
    }

    // consume binders and return a function that constructs a BinderFormula given the inner formula
    val binders: Syntax[Formula => Formula] = many(accept(BinderKind) {
      case ExistsToken => Exists
      case ExistsOneToken => ExistsOne
      case ForallToken => Forall
    } ~ accept(FunctionOrPredicateKind) {
      case ConstantToken(id) => VariableLabel(id)
      case SchematicToken(id) => VariableLabel(id)
    } ~ elem(DotKind).unit(DotToken).skip) map getBinderFormulaConstructor

    lazy val formula: Syntax[Formula] = recursive {
      (binders ~ connectorFormula ~ opt(toplevelConnector ~ connectorFormula)) map { case binderFormulaConstructor ~ f ~ rest =>
        rest match {
          case Some(conn ~ f2) => binderFormulaConstructor(ConnectorFormula(conn, Seq(f, f2)))
          case None => binderFormulaConstructor(f)
        }
      }
    }
    ///////////////////////////////////////////////////////////////////

    val parser: FormulaParser.Parser[FOL.Formula] = Parser(formula)

    val termParser: FormulaParser.Parser[FOL.Term] = Parser(term)

    def apply(it: Iterator[Token]): ParseResult[Formula] = parseFormula(it)

    def parseFormula(it: Iterator[Token]): ParseResult[Formula] = parser(it)

    def parseTerm(it: Iterator[Token]): ParseResult[Term] = termParser(it)
  }
}
