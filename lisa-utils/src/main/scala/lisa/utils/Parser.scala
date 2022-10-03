package lisa.utils

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.kernel.fol.FOL.equality
import lisa.kernel.proof.SequentCalculus.*
import scallion.*
import scallion.util.Unfolds.unfoldRight
import silex.*

object Parser {

  class ParserException(msg: String) extends Exception(msg)
  object UnreachableException extends ParserException("Internal error: expected unreachable")
  class PrintFailedException(inp: Sequent | Formula | Term) extends ParserException(s"Printing of $inp failed unexpectedly")

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

  def printSequent(s: Sequent): String = SequentParser.printSequent(s).getOrElse(throw PrintFailedException(s))

  def printFormula(f: Formula): String = SequentParser.printFormula(f).getOrElse(throw PrintFailedException(f))

  def printTerm(t: Term): String = SequentParser.printTerm(t).getOrElse(throw PrintFailedException(t))

  private[Parser] object SequentLexer extends Lexers with CharLexers {
    sealed abstract class FormulaToken(stringRepr: String) {
      override def toString: String = stringRepr
    }

    case object ForallToken extends FormulaToken(Forall.id)

    case object ExistsOneToken extends FormulaToken(ExistsOne.id)

    case object ExistsToken extends FormulaToken(Exists.id)

    case object DotToken extends FormulaToken(".")

    case object AndToken extends FormulaToken(And.id)

    case object OrToken extends FormulaToken(Or.id)

    case object ImpliesToken extends FormulaToken(Implies.id)

    case object IffToken extends FormulaToken(Iff.id)

    case object NegationToken extends FormulaToken(Neg.id)

    case object EqualityToken extends FormulaToken(equality.id)

    // Constant functions and predicates
    case class ConstantToken(id: String) extends FormulaToken(id)

    // Variables, schematic functions and predicates
    case class SchematicToken(id: String) extends FormulaToken("?" + id)

    case class ParenthesisToken(isOpen: Boolean) extends FormulaToken(if (isOpen) "(" else ")")

    case object CommaToken extends FormulaToken(",")

    case object SemicolonToken extends FormulaToken(";")

    case object SequentToken extends FormulaToken("⊢")

    case object SpaceToken extends FormulaToken(" ")

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

    def unapply(tokens: Iterator[Token]): String = {
      val space = " "
      tokens
        .foldLeft(Nil: List[String]) {
          // Sequent token is the only separator that can have an empty left side; in this case, omit the space before
          case (Nil, SequentToken) => SequentToken.toString :: space :: Nil
          case (l, t) =>
            t match {
              // do not require spaces
              case NegationToken | ConstantToken(_) | SchematicToken(_) | ParenthesisToken(_) | SpaceToken => l :+ t.toString
              // space after: quantifiers and separators
              case ForallToken | ExistsToken | ExistsOneToken | DotToken | CommaToken | SemicolonToken => l :+ t.toString :+ space
              // space before and after: equality, connectors, sequent symbol
              case EqualityToken | AndToken | OrToken | ImpliesToken | IffToken | SequentToken => l :+ space :+ t.toString :+ space
            }
        }
        .mkString
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

    import SequentLexer._
    type Token = FormulaToken
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
    val toplevelConnector: Syntax[Implies.type | Iff.type] = accept(TopLevelConnectorKind)(
      {
        case ImpliesToken => Implies
        case IffToken => Iff
      },
      {
        case Implies => Seq(ImpliesToken)
        case Iff => Seq(IffToken)
      }
    )

    val negation: Syntax[Neg.type] = accept(NegationKind)({ case NegationToken => Neg }, { case Neg => Seq(NegationToken) })
    ///////////////////////////////////////////////////////////////////

    //////////////////////// TERMS ////////////////////////////////////
    lazy val args: Syntax[Seq[Term]] = recursive(open.skip ~ repsep(term, comma) ~ closed.skip)

    def invertTerm(t: Term): Token ~ Option[Seq[Term]] = t match {
      case VariableTerm(label) => SchematicToken(label.id) ~ None
      case FunctionTerm(label, args) =>
        val optArgs = args match {
          case Seq() => None
          case _ => Some(args)
        }
        label match {
          case ConstantFunctionLabel(id, _) => ConstantToken(id) ~ optArgs
          case SchematicFunctionLabel(id, _) => SchematicToken(id) ~ optArgs
        }
    }

    lazy val term: Syntax[Term] = recursive(
      (elem(FunctionOrPredicateKind) ~ opt(args)).map(
        {
          case ConstantToken(id) ~ maybeArgs =>
            val args = maybeArgs.getOrElse(Seq())
            FunctionTerm(ConstantFunctionLabel(id, args.length), args)
          case SchematicToken(id) ~ Some(args) => FunctionTerm(SchematicFunctionLabel(id, args.length), args)
          case SchematicToken(id) ~ None => VariableTerm(VariableLabel(id))
          case _ => throw UnreachableException
        },
        t => Seq(invertTerm(t))
      )
    )
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

    val predicate: Syntax[PredicateFormula] = (elem(FunctionOrPredicateKind) ~ opt(args) ~ opt(eq.skip ~ elem(FunctionOrPredicateKind) ~ opt(args))).map(
      {
        // predicate application
        case ConstantToken(id) ~ maybeArgs ~ None =>
          val args = maybeArgs.getOrElse(Seq())
          PredicateFormula(ConstantPredicateLabel(id, args.size), args)
        case SchematicToken(id) ~ Some(args) ~ None => PredicateFormula(SchematicNPredicateLabel(id, args.size), args)
        case SchematicToken(id) ~ None ~ None =>
          PredicateFormula(VariableFormulaLabel(id), Seq())

        // equality of two function applications
        case fun1 ~ args1 ~ Some(fun2 ~ args2) =>
          PredicateFormula(FOL.equality, Seq(createFunctionTerm(fun1, args1.getOrElse(Seq())), createFunctionTerm(fun2, args2.getOrElse(Seq()))))

        case _ => throw UnreachableException
      },
      { case PredicateFormula(label, args) =>
        label match {
          case FOL.equality =>
            args match {
              case Seq(first, second) => Seq(invertTerm(first) ~ Some(invertTerm(second)))
              case _ => Seq()
            }
          case other =>
            val predicateApp = other match {
              case ConstantPredicateLabel(id, 0) => ConstantToken(id) ~ None
              case ConstantPredicateLabel(id, _) => ConstantToken(id) ~ Some(args)
              case VariableFormulaLabel(id) => SchematicToken(id) ~ None
              case SchematicNPredicateLabel(id, _) => SchematicToken(id) ~ Some(args)
            }
            Seq(predicateApp ~ None)
        }
      }
    )

    val negated: Syntax[ConnectorFormula] = recursive {
      (negation ~ subformula).map(
        { case n ~ f =>
          ConnectorFormula(n, Seq(f))
        },
        {
          case ConnectorFormula(Neg, Seq(f)) => Seq(Neg ~ f)
          case _ => throw UnreachableException
        }
      )
    }

    val and: Syntax[ConnectorLabel] = elem(AndKind).map[ConnectorLabel](
      {
        case AndToken => And
        case _ => throw UnreachableException
      },
      {
        case And => Seq(AndToken)
        case _ => throw UnreachableException
      }
    )

    val or: Syntax[ConnectorLabel] = elem(OrKind).map[ConnectorLabel](
      {
        case OrToken => Or
        case _ => throw UnreachableException
      },
      {
        case Or => Seq(OrToken)
        case _ => throw UnreachableException
      }
    )

    // 'and' has higher priority than 'or'
    val connectorFormula: Syntax[Formula] = operators(subformula)(
      and is LeftAssociative,
      or is LeftAssociative
    )(
      (l, conn, r) => ConnectorFormula(conn, Seq(l, r)),
      {
        case ConnectorFormula(conn, Seq(l, r)) =>
          (l, conn, r)
        case ConnectorFormula(conn, l +: rest) if rest.nonEmpty =>
          val last = rest.last
          val leftSide = rest.dropRight(1)
          // parser only knows about connector formulas of two arguments, so we unfold the formula of many arguments to
          // multiple nested formulas of two arguments
          (leftSide.foldLeft(l)((f1, f2) => ConnectorFormula(conn, Seq(f1, f2))), conn, last)
      }
    )

    val binderLabel: Syntax[BinderLabel] = accept(BinderKind)(
      {
        case ExistsToken => Exists
        case ExistsOneToken => ExistsOne
        case ForallToken => Forall
      },
      {
        case Exists => Seq(ExistsToken)
        case ExistsOne => Seq(ExistsOneToken)
        case Forall => Seq(ForallToken)
      }
    )

    val boundVariable: Syntax[VariableLabel] = accept(FunctionOrPredicateKind)(
      {
        case ConstantToken(id) => VariableLabel(id)
        case SchematicToken(id) => VariableLabel(id)
      },
      { case VariableLabel(id) =>
        Seq(SchematicToken(id))
      }
    )

    val binder: Syntax[BinderLabel ~ VariableLabel] = binderLabel ~ boundVariable ~ elem(DotKind).unit(DotToken).skip

    val iffImpliesFormula: Syntax[Formula] = (connectorFormula ~ opt(toplevelConnector ~ connectorFormula)).map[Formula](
      {
        case left ~ Some(c ~ right) => ConnectorFormula(c, Seq(left, right))
        case f ~ None => f
      },
      {
        case ConnectorFormula(c @ (Iff | Implies), Seq(left, right)) => Seq(left ~ Some(c ~ right))
        case f => Seq(f ~ None)
      }
    )

    lazy val formula: Syntax[Formula] = recursive {
      prefixes(binder, iffImpliesFormula)(
        { case (label ~ variable, f) => BinderFormula(label, variable, f) },
        { case BinderFormula(label, variable, f) =>
          (label ~ variable, f)
        }
      )
    }
    ///////////////////////////////////////////////////////////////////

    val sequent: Syntax[Sequent] = (repsep(formula, semicolon) ~ opt(sequentSymbol.skip ~ repsep(formula, semicolon))).map[Sequent](
      {
        case left ~ Some(right) => Sequent(left.toSet, right.toSet)
        case right ~ None => Sequent(Set(), right.toSet)
      },
      {
        case Sequent(Seq(), right) => Seq(right.toSeq ~ None)
        case Sequent(left, right) => Seq(left.toSeq ~ Some(right.toSeq))
      }
    )

    val parser: Parser[Sequent] = Parser(sequent)
    val printer: PrettyPrinter[Sequent] = PrettyPrinter(sequent)

    val formulaParser: SequentParser.Parser[Formula] = Parser(formula)
    val formulaPrinter: SequentParser.PrettyPrinter[Formula] = PrettyPrinter(formula)

    val termParser: SequentParser.Parser[Term] = Parser(term)
    val termPrinter: SequentParser.PrettyPrinter[Term] = PrettyPrinter(term)

    def apply(it: Iterator[Token]): ParseResult[Sequent] = parseSequent(it)

    def unapply(s: Sequent): Option[String] = printSequent(s)

    def parseSequent(it: Iterator[Token]): ParseResult[Sequent] = parser(it)
    def printSequent(s: Sequent): Option[String] = printer(s).map(SequentLexer.unapply)

    def parseFormula(it: Iterator[Token]): ParseResult[Formula] = formulaParser(it)
    def printFormula(f: Formula): Option[String] = formulaPrinter(f).map(SequentLexer.unapply)

    def parseTerm(it: Iterator[Token]): ParseResult[Term] = termParser(it)

    def printTerm(t: Term): Option[String] = termPrinter(t).map(SequentLexer.unapply)
  }
}
