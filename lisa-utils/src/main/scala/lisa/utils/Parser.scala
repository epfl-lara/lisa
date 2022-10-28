package lisa.utils

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.kernel.fol.FOL.equality
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.False
import scallion.*
import scallion.util.Unfolds.unfoldRight
import silex.*

object Parser {
  enum Notation {
    case Prefix, Infix
  }

  abstract class Label(val id: String, val notation: Notation)

  case class InfixLabel(override val id: String) extends Label(id, Notation.Infix)

  case class PrefixLabel(override val id: String) extends Label(id, Notation.Prefix)

  case class CanonicalLabel(print: Label, internal: Label)

  def equivalentLabelsToMap(labels: List[String], print: Label, internal: Label): Map[String, CanonicalLabel] =
    labels.map(_ -> CanonicalLabel(print, internal)).toMap

  private val mapping: Map[String, CanonicalLabel] =
    equivalentLabelsToMap("elem" :: "in" :: "∊" :: Nil, InfixLabel("∊"), PrefixLabel("elem")) ++
      equivalentLabelsToMap("subset_of" :: "subset" :: "⊆" :: Nil, InfixLabel("⊆"), PrefixLabel("subset_of")) ++
      equivalentLabelsToMap("sim" :: "same_cardinality" :: "≈" :: Nil, InfixLabel("≈"), PrefixLabel("same_cardinality")) ++
      equivalentLabelsToMap("=" :: Nil, InfixLabel("="), InfixLabel("="))

  def getPrintName(id: String): Option[Label] = mapping.get(id).map(_.print)

  def getInternalName(id: String): String = mapping.get(id).map(_.internal.id).getOrElse(id)

  class ParserException(msg: String) extends Exception(msg)
  object UnreachableException extends ParserException("Internal error: expected unreachable")
  class PrintFailedException(inp: Sequent | Formula | Term) extends ParserException(s"Printing of $inp failed unexpectedly")

  def isInfixPredicate(id: String): Boolean = Set("=", "∊", "⊂", "⊆").contains(id)

  /**
   * Parses a sequent from a string. A sequent consists of the left and right side, separated by `⊢` or `|-`.
   * Left and right sides consist of formulas, separated by `;`.
   *
   * @see Parser#parseFormula
   * @param s string representation of the sequent
   * @return parsed sequent on success, throws an exception when unexpected input or end of input.
   */
  def parseSequent(s: String): Sequent =
    extractParseResult(SequentParser.parseSequent(SequentLexer(s.iterator)))

  /**
   * Parses a formula from a string. A formula can be:
   * <p> - a bound formula: `∀ ?x. f`, `∃ ?x. f`, `∃! ?x. f`. A binder binds the entire formula until the end of the scope (a closing parenthesis or the end of string).
   * <p> - two formulas, connected by `↔` or `⇒`. Iff / implies bind less tight than and / or.
   * <p> - a conjunction or disjunction of arbitrary number of formulas. `∧` binds tighter than `∨`.
   * <p> - negated formula.
   * <p> - equality of two formulas: `f1 = f2`.
   * <p> - a constant `p(a)` or schematic `?p(a)` predicate application to arbitrary number of term arguments.
   * <p> - boolean constant: `⊤` or `⊥`.
   *
   * @param s string representation of the formula
   * @return parsed formula on success, throws an exception when unexpected input or end of input.
   */
  def parseFormula(s: String): Formula =
    extractParseResult(SequentParser.parseFormula(SequentLexer(s.iterator)))

  /**
   * Parses a term from a string. A term is a constant `c`, a schematic variable `?x` or an application of a constant `f(a)`
   * or a schematic `?f(a)` function to other terms.
   *
   * @param s string representation of the term
   * @return parsed term on success, throws an exception when unexpected input or end of input.
   */
  def parseTerm(s: String): Term =
    extractParseResult(SequentParser.parseTerm(SequentLexer(s.iterator)))

  private def extractParseResult[T](r: SequentParser.ParseResult[T]): T = r match {
    case SequentParser.Parsed(value, _) => value
    // TODO: at position
    case SequentParser.UnexpectedToken(token, _) => throw ParserException(s"Unexpected input: ${SequentLexer.unapply(Iterator(token))}")
    case SequentParser.UnexpectedEnd(_) => throw ParserException(s"Unexpected end of input")
  }

  /**
   * Returns a string representation of the sequent. Empty set of formulas on the left side is not printed.
   * Empty set of formulas on the right side is represented as `⊥` (false).
   *
   * @param s sequent to print
   * @return string representation of the sequent, or the smallest component thereof, on which printing failed
   */
  def printSequent(s: Sequent): String = SequentParser
    .printSequent(s)
    .getOrElse({
      // attempt to print individual formulas. It might throw a more detailed PrintFailedException
      s.left.foreach(printFormula)
      s.right.foreach(printFormula)
      throw PrintFailedException(s)
    })

  /**
   * @param f formula to print
   * @return string representation of the formula, or the smallest component thereof, on which printing failed
   */
  def printFormula(f: Formula): String = SequentParser
    .printFormula(f)
    .getOrElse({
      f match {
        case PredicateFormula(_, args) => args.foreach(printTerm)
        case ConnectorFormula(_, args) => args.foreach(printFormula)
        case BinderFormula(_, _, inner) => printFormula(inner)
      }
      throw PrintFailedException(f)
    })

  /**
   * @param t term to print
   * @return string representation of the term, or the smallest component thereof, on which printing failed
   */
  def printTerm(t: Term): String = SequentParser
    .printTerm(t)
    .getOrElse({
      t match {
        case Term(_, args) => args.foreach(printTerm)
        case VariableTerm(_) => ()
      }
      throw PrintFailedException(t)
    })

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

    case object TrueToken extends FormulaToken("⊤")

    case object FalseToken extends FormulaToken("⊥")

    case class InfixPredicateToken(id: String) extends FormulaToken(id)

    // Constant functions and predicates
    case class ConstantToken(id: String) extends FormulaToken(id)

    // Variables, schematic functions and predicates
    case class SchematicToken(id: String) extends FormulaToken(schematicSymbol + id)

    case class ParenthesisToken(isOpen: Boolean) extends FormulaToken(if (isOpen) "(" else ")")

    case object CommaToken extends FormulaToken(",")

    case object SemicolonToken extends FormulaToken(";")

    case object SequentToken extends FormulaToken("⊢")

    case object SpaceToken extends FormulaToken(" ")

    type Token = FormulaToken
    // TODO: add positions ==> ranges to tokens
    type Position = Unit

    val escapeChar = '`'
    val pathSeparator = '$'
    private val schematicSymbol = "'"

    private val letter = elem(_.isLetter)
    private val variableLike = letter ~ many(elem(c => c.isLetterOrDigit || c == '_'))
    private val number = many1(elem(_.isDigit))
    private val escaped = elem(escapeChar) ~ many1(elem(_ != escapeChar)) ~ elem(escapeChar)
    private val arbitrarySymbol = elem(!_.isWhitespace)
    private val symbolSequence = many1(oneOf("*/+-^:<>#%&@"))
    private val path = many1(many1(letter) ~ elem(pathSeparator))

    private val lexer = Lexer(
      elem('∀') |> { _ => ForallToken },
      word("∃!") |> { _ => ExistsOneToken },
      elem('∃') |> { _ => ExistsToken },
      elem('.') |> { _ => DotToken },
      elem('∧') | word("/\\") |> { _ => AndToken },
      elem('∨') | word("\\/") |> { _ => OrToken },
      word(Implies.id) | word("=>") | word("==>") | elem('→') |> { _ => ImpliesToken },
      word(Iff.id) | word("<=>") | word("<==>") | elem('⟷') | elem('↔') |> { _ => IffToken },
      elem('⊤') | elem('T') | word("True") | word("true") |> { _ => TrueToken },
      elem('⊥') | elem('F') | word("False") | word("false") |> { _ => FalseToken },
      elem('¬') | elem('!') |> { _ => NegationToken },
      elem('(') |> ParenthesisToken(true),
      elem(')') |> ParenthesisToken(false),
      elem(',') |> CommaToken,
      elem(';') |> SemicolonToken,
      elem('⊢') | word("|-") |> SequentToken,
      many1(whiteSpace) |> SpaceToken,
      word(schematicSymbol) ~ variableLike |> { cs =>
        // drop the '
        SchematicToken(cs.drop(1).mkString)
      },
      // Currently the path is merged into the id on the lexer level. When qualified ids are supported, this should be
      // lifted into the parser.
      opt(path) ~ (variableLike | number | arbitrarySymbol | symbolSequence | escaped) |> { cs => ConstantToken(cs.filter(_ != escapeChar).mkString) }
    ) onError { (cs, _) =>
      throw ParserException(s"Unexpected input: ${cs.mkString}")
    }

    def apply(it: Iterator[Char]): Iterator[Token] = {
      val source = Source.fromIterator(it, NoPositioner)
      lexer(source)
        .filter(_ != SpaceToken)
        .map({
          case ConstantToken(id) if isInfixPredicate(id) => InfixPredicateToken(id)
          case t => t
        })
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
              case ForallToken | ExistsToken | ExistsOneToken | NegationToken | ConstantToken(_) | SchematicToken(_) | TrueToken | FalseToken | ParenthesisToken(_) | SpaceToken => l :+ t.toString
              // space after: separators
              case DotToken | CommaToken | SemicolonToken => l :+ t.toString :+ space
              // space before and after: equality, connectors, sequent symbol
              case InfixPredicateToken(_) | AndToken | OrToken | ImpliesToken | IffToken | SequentToken => l :+ space :+ t.toString :+ space
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
    case object BooleanConstantKind extends TokenKind
    case object FunctionOrPredicateKind extends TokenKind
    case object InfixPredicateKind extends TokenKind
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
      case TrueToken | FalseToken => BooleanConstantKind
      case _: ConstantToken | _: SchematicToken => FunctionOrPredicateKind
      case _: InfixPredicateToken => InfixPredicateKind
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

    val INFIX_ARITY = 2
    val infixPredicateLabel: Syntax[ConstantPredicateLabel] = accept(InfixPredicateKind)(
      {
        case InfixPredicateToken(id) => ConstantPredicateLabel(getInternalName(id), INFIX_ARITY)
        case _ => throw UnreachableException
      },
      {
        case ConstantPredicateLabel(id, INFIX_ARITY) if getPrintName(id).map(_.notation == Notation.Infix).getOrElse(isInfixPredicate(id)) =>
          val printName = getPrintName(id).map(_.id).getOrElse(id)
          Seq(InfixPredicateToken(printName))
        case _ => throw UnreachableException
      }
    )

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
      case Term(label, args) =>
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
            Term(ConstantFunctionLabel(id, args.length), args)
          case SchematicToken(id) ~ Some(args) => Term(SchematicFunctionLabel(id, args.length), args)
          case SchematicToken(id) ~ None => VariableTerm(VariableLabel(id))
          case _ => throw UnreachableException
        },
        t => Seq(invertTerm(t))
      )
    )
    ///////////////////////////////////////////////////////////////////

    //////////////////////// FORMULAS /////////////////////////////////
    // can appear without parentheses
    lazy val simpleFormula: Syntax[Formula] = predicate.up[Formula] | negated.up[Formula] | bool.up[Formula]
    lazy val subformula: Syntax[Formula] = simpleFormula | open.skip ~ formula ~ closed.skip

    def createTerm(label: Token, args: Seq[Term]): Term = label match {
      case ConstantToken(id) => Term(ConstantFunctionLabel(id, args.size), args)
      case SchematicToken(id) =>
        args match {
          case Seq() => VariableTerm(VariableLabel(id))
          case _ => Term(SchematicFunctionLabel(id, args.size), args)
        }
      case _ => throw UnreachableException
    }

    val bool: Syntax[ConnectorFormula] = accept(BooleanConstantKind)(
      {
        case TrueToken => ConnectorFormula(And, Seq())
        case FalseToken => ConnectorFormula(Or, Seq())
      },
      {
        case ConnectorFormula(And, Seq()) => Seq(TrueToken)
        case ConnectorFormula(Or, Seq()) => Seq(FalseToken)
        case _ => throw UnreachableException
      }
    )

    val predicate: Syntax[PredicateFormula] = (elem(FunctionOrPredicateKind) ~ opt(args) ~ opt(infixPredicateLabel ~ term)).map(
      {
        // predicate application
        case ConstantToken(id) ~ maybeArgs ~ None =>
          val args = maybeArgs.getOrElse(Seq())
          PredicateFormula(ConstantPredicateLabel(getInternalName(id), args.size), args)
        case SchematicToken(id) ~ Some(args) ~ None => PredicateFormula(SchematicPredicateLabel(getInternalName(id), args.size), args)
        case SchematicToken(id) ~ None ~ None =>
          PredicateFormula(VariableFormulaLabel(getInternalName(id)), Seq())

        // infix relation of two function applications
        case fun1 ~ args1 ~ Some(pred ~ term2) =>
          PredicateFormula(pred, Seq(createTerm(fun1, args1.getOrElse(Seq())), term2))

        case _ => throw UnreachableException
      },
      {
        case PredicateFormula(label @ ConstantPredicateLabel(id, INFIX_ARITY), Seq(first, second)) if getPrintName(id).map(_.notation == Notation.Infix).getOrElse(isInfixPredicate(id)) =>
          Seq(invertTerm(first) ~ Some(label ~ second))
        case PredicateFormula(label, args) =>
          val (canonicalId, isInfix) = getPrintName(label.id).map(l => (l.id, l.notation == Notation.Infix)).getOrElse(label.id, false)
          if (isInfix && args.size == INFIX_ARITY) {
            args match {
              case Seq(first, second) => Seq(invertTerm(first) ~ Some(ConstantPredicateLabel(canonicalId, INFIX_ARITY) ~ second))
              case _ => throw UnreachableException
            }
          } else {
            val prefixApp = label match {
              case VariableFormulaLabel(id) => SchematicToken(canonicalId) ~ None
              case SchematicPredicateLabel(id, _) => SchematicToken(canonicalId) ~ Some(args)
              case ConstantPredicateLabel(id, 0) => ConstantToken(canonicalId) ~ None
              case ConstantPredicateLabel(id, _) => ConstantToken(canonicalId) ~ Some(args)
            }
            Seq(prefixApp ~ None)
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
        case ConnectorFormula((And | Or), Seq(f)) => Seq(f ~ None)
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
        // TODO: use constant
        case Sequent(left, Seq()) => Seq(left.toSeq ~ Some(Seq(False)))
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
