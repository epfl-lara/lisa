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
  //////////////////////////////// EQUIVALENT LABELS, INFIX CONTROL ///////////////////////////////
  case class CanonicalId(print: String, internal: String)

  def equivalentLabelsToMap(equivalentLabels: List[String], print: String, internal: String): Map[String, CanonicalId] =
    (print :: internal :: equivalentLabels).map(_ -> CanonicalId(print, internal)).toMap

  // TODO: grow the mapping as we discover / introduce more synonyms
  // The mapping stores the information about synonymous strings for the same id, mapping a string to its canonical
  // form (the id that is used to construct the `ConstantLabel`) and the printable form (the preferred synonym to
  // display in strings).
  private val SynonymToCanonical: Map[String, CanonicalId] =
    equivalentLabelsToMap("elem" :: "in" :: Nil, "∊", "elem") ++
      equivalentLabelsToMap("subset_of" :: "subset" :: Nil, "⊆", "subset_of") ++
      equivalentLabelsToMap("sim" :: "same_cardinality" :: Nil, "≈", "same_cardinality")

  /**
   * @return the preferred way to output this id, if available, otherwise the id itself.
   */
  def getPrintName(id: String): String = SynonymToCanonical.get(id).map(_.print).getOrElse(id)

  /**
   * @return the synonym of `id` that is used to construct the corresponding `ConstantPredicateLabel` or
   *         `ConstantFunctionLabel`. If not available, `id` has no known synonyms, so return `id` itself.
   */
  def getInternalName(id: String): String = SynonymToCanonical.get(id).map(_.internal).getOrElse(id)
  /////////////////////////////////////////////////////////////////////////////////////////////////
  // TODO: support more infix ops, potentially determine if an op is infix without listing all infix ones
  def isInfix(id: String): Boolean = Set("=", "∊", "⊂", "⊆", "+", "<").contains(id)

  class ParserException(msg: String) extends Exception(msg)
  object UnreachableException extends ParserException("Internal error: expected unreachable")
  class PrintFailedException(inp: Sequent | Formula | Term) extends ParserException(s"Printing of $inp failed unexpectedly")

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
   * <p> - schematic connector formula: `?c(f1, f2, f3)`.
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

    case class InfixToken(id: String) extends FormulaToken(id)

    // Constant functions and predicates
    case class ConstantToken(id: String) extends FormulaToken(id)

    // Variables, schematic functions and predicates
    case class SchematicToken(id: String) extends FormulaToken(schematicSymbol + id)

    // Schematic connector (prefix notation is expected)
    case class SchematicConnectorToken(id: String) extends FormulaToken(schematicConnectorSymbol + id)

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
    private val schematicConnectorSymbol = "?"

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
      word(schematicConnectorSymbol) ~ variableLike |> { cs =>
        SchematicConnectorToken(cs.drop(1).mkString)
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
          case ConstantToken(id) if isInfix(id) => InfixToken(id)
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
              case ForallToken | ExistsToken | ExistsOneToken | NegationToken | ConstantToken(_) | SchematicToken(_) | SchematicConnectorToken(_) | TrueToken | FalseToken | ParenthesisToken(_) |
                  SpaceToken =>
                l :+ t.toString
              // space after: separators
              case DotToken | CommaToken | SemicolonToken => l :+ t.toString :+ space
              // space before and after: equality, connectors, sequent symbol
              case InfixToken(_) | AndToken | OrToken | ImpliesToken | IffToken | SequentToken => l :+ space :+ t.toString :+ space
            }
        }
        .mkString
    }
  }

  /**
   * Termula represents parser-level union of terms and formulas.
   * After parsing, the termula can be converted either to a term or to a formula:
   * <p> - to be converted to a term, termula must consist only of function applications;
   * <p> - to be converted to a formula, `args` of the termula are interpreted as formulas until a predicate application is observed;
   * `args` of the predicate application are terms.
   *
   * <p> Convention: since the difference between `TermLabel`s and `PredicateLabel`s is purely semantic and Termula needs
   * FormulaLabels (because of connector and binder labels), all TermLabels are translated to the corresponding
   * PredicateLabels (see [[toTermula]]).
   *
   * @param label `PredicateLabel` for predicates and functions, `ConnectorLabel` or `BinderLabel`
   * @param args Predicate / function arguments for `PredicateLabel`, connected formulas for `ConnectorLabel`,
   *             `Seq(VariableFormulaLabel(bound), inner)` for `BinderLabel`
   */
  case class Termula(label: FOL.FormulaLabel, args: Seq[Termula]) {
    def toTerm: Term = label match {
      case t: ConstantPredicateLabel => Term(ConstantFunctionLabel(t.id, t.arity), args.map(_.toTerm))
      case t: SchematicPredicateLabel => Term(SchematicFunctionLabel(t.id, t.arity), args.map(_.toTerm))
      case v: VariableFormulaLabel => Term(VariableLabel(v.id), Seq())
      case _ => throw ParserException(s"Expected term, got $this")
    }

    def toFormula: Formula = label match {
      case p: PredicateLabel => PredicateFormula(p, args.map(_.toTerm))
      case c: ConnectorLabel => ConnectorFormula(c, args.map(_.toFormula))
      case b: BinderLabel =>
        args match {
          case Seq(Termula(v: VariableFormulaLabel, Seq()), f) => BinderFormula(b, VariableLabel(v.id), f.toFormula)
          case _ => throw ParserException(s"Wrong binder format: expected 2 arguments: bound VariableFormulaLabel and inner termula, got $args")
        }
    }
  }

  extension (f: Formula) {
    def toTermula: Termula = f match {
      case PredicateFormula(label, args) => Termula(label, args.map(_.toTermula))
      case ConnectorFormula(label, args) => Termula(label, args.map(_.toTermula))
      case BinderFormula(label, bound, inner) => Termula(label, Seq(Termula(VariableFormulaLabel(bound.id), Seq()), inner.toTermula))
    }
  }

  extension (t: Term) {
    def toTermula: Termula = {
      val newLabel = t.label match {
        case ConstantFunctionLabel(id, arity) => ConstantPredicateLabel(id, arity)
        case SchematicFunctionLabel(id, arity) => SchematicPredicateLabel(id, arity)
        case VariableLabel(id) => VariableFormulaLabel(id)
      }
      Termula(newLabel, t.args.map(_.toTermula))
    }
  }

  case class TermulaSequent(left: Set[Termula], right: Set[Termula]) {
    def toSequent: Sequent = Sequent(left.map(_.toFormula), right.map(_.toFormula))
  }

  extension (s: Sequent) {
    def toTermulaSequent: TermulaSequent = TermulaSequent(s.left.map(_.toTermula), s.right.map(_.toTermula))
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
    case object SchematicConnectorKind extends TokenKind
    case object IdKind extends TokenKind
    case object InfixKind extends TokenKind
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
      case _: SchematicConnectorToken => SchematicConnectorKind
      case _: ConstantToken | _: SchematicToken => IdKind
      case _: InfixToken => InfixKind
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

    val INFIX_ARITY = 2
    val infixLabel: Syntax[ConstantPredicateLabel] = accept(InfixKind)(
      {
        case InfixToken(id) => ConstantPredicateLabel(getInternalName(id), INFIX_ARITY)
        case _ => throw UnreachableException
      },
      {
        case ConstantPredicateLabel(id, INFIX_ARITY) if isInfix(getPrintName(id)) =>
          val printName = getPrintName(id)
          Seq(InfixToken(printName))
        case _ => throw UnreachableException
      }
    )
    ///////////////////////////////////////////////////////////////////

    //////////////////////// TERMULAS /////////////////////////////////
    // can appear without parentheses
    lazy val simpleTermula: Syntax[Termula] = application | negated | bool | schematicConnectorFormula
    lazy val subtermula: Syntax[Termula] = simpleTermula | startsWithParenthesis
    lazy val startsWithParenthesis: Syntax[Termula] = recursive(
      (open.skip ~ termula ~ closed.skip ~ opt(infixLabel ~ subtermula)).map(
        {
          case f ~ None => f
          case f1 ~ Some(label ~ f2) => Termula(label, Seq(f1, f2))
        },
        {
          case Termula(c @ ConstantPredicateLabel(id, INFIX_ARITY), Seq(f1, f2)) if isInfix(getPrintName(id)) => Seq(f1 ~ Some(c ~ f2))
          case f => Seq(f ~ None)
        }
      )
    )

    val bool: Syntax[Termula] = accept(BooleanConstantKind)(
      {
        case TrueToken => Termula(And, Seq())
        case FalseToken => Termula(Or, Seq())
      },
      {
        case Termula(And, Seq()) => Seq(TrueToken)
        case Termula(Or, Seq()) => Seq(FalseToken)
        case _ => throw UnreachableException
      }
    )

    lazy val args: Syntax[Seq[Termula]] = recursive(open.skip ~ repsep(termula, comma) ~ closed.skip)

    def reconstructPrefixApplication(t: Termula): Token ~ Option[Seq[Termula]] = t.label match {
      case VariableFormulaLabel(id) => SchematicToken(id) ~ None
      case SchematicPredicateLabel(id, _) => SchematicToken(id) ~ Some(t.args)
      case ConstantPredicateLabel(id, arity) => ConstantToken(getPrintName(id)) ~ (if (arity == 0) None else Some(t.args))
      case _ => throw UnreachableException
    }

    val prefixApplication: Syntax[Termula] = (elem(IdKind) ~ opt(args)).map(
      { case p ~ optArgs =>
        val args = optArgs.getOrElse(Seq())
        val l = p match {
          case ConstantToken(id) => ConstantPredicateLabel(getInternalName(id), args.size)
          case SchematicToken(id) =>
            if (args.isEmpty) VariableFormulaLabel(id) else SchematicPredicateLabel(id, args.size)
          case _ => throw UnreachableException
        }
        Termula(l, args)
      },
      {
        case t @ Termula(_: PredicateLabel, _) => Seq(reconstructPrefixApplication(t))
        case _ => throw UnreachableException
      }
    )

    lazy val application: Syntax[Termula] =
      recursive(
        (prefixApplication ~ opt(infixLabel ~ subtermula)).map(
          {
            case p ~ None => p
            case p1 ~ Some(label ~ p2) => Termula(label, Seq(p1, p2))
          },
          {
            case Termula(c @ ConstantPredicateLabel(id, INFIX_ARITY), Seq(f1 @ Termula(_: PredicateLabel, _), f2)) if isInfix(getPrintName(id)) =>
              Seq(f1 ~ Some(c ~ f2))
            case t @ Termula(_: PredicateLabel, _) => Seq(t ~ None)
            case _ => throw UnreachableException
          }
        )
      )

    val negated: Syntax[Termula] = recursive {
      (negation ~ subtermula).map(
        { case n ~ f =>
          Termula(n, Seq(f))
        },
        {
          case Termula(Neg, Seq(f)) => Seq(Neg ~ f)
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
    val connectorTermula: Syntax[Termula] = operators(subtermula)(
      and is LeftAssociative,
      or is LeftAssociative
    )(
      (l, conn, r) => Termula(conn, Seq(l, r)),
      {
        case Termula(conn: ConnectorLabel, Seq(l, r)) =>
          (l, conn, r)
        case Termula(conn: ConnectorLabel, l +: rest) if rest.nonEmpty =>
          val last = rest.last
          val leftSide = rest.dropRight(1)
          // parser only knows about connector formulas of two arguments, so we unfold the formula of many arguments to
          // multiple nested formulas of two arguments
          (leftSide.foldLeft(l)((f1, f2) => Termula(conn, Seq(f1, f2))), conn, last)
      }
    )

    lazy val schematicConnectorFormula: Syntax[Termula] = (elem(SchematicConnectorKind) ~ args).map(
      {
        case SchematicConnectorToken(id) ~ args => Termula(SchematicConnectorLabel(id, args.size), args)
        case _ => throw UnreachableException
      },
      {
        case Termula(SchematicConnectorLabel(id, _), args) => Seq(SchematicConnectorToken(id) ~ args)
        case _ => throw UnreachableException
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

    val boundVariable: Syntax[VariableFormulaLabel] = accept(IdKind)(
      {
        case ConstantToken(id) => VariableFormulaLabel(id)
        case SchematicToken(id) => VariableFormulaLabel(id)
      },
      { case VariableFormulaLabel(id) =>
        Seq(SchematicToken(id))
      }
    )

    val binder: Syntax[BinderLabel ~ VariableFormulaLabel] = binderLabel ~ boundVariable ~ elem(DotKind).unit(DotToken).skip

    val iffImpliesTermula: Syntax[Termula] = (connectorTermula ~ opt(toplevelConnector ~ connectorTermula)).map[Termula](
      {
        case left ~ Some(c ~ right) => Termula(c, Seq(left, right))
        case f ~ None => f
      },
      {
        case Termula(c @ (Iff | Implies), Seq(left, right)) => Seq(left ~ Some(c ~ right))
        case Termula((And | Or), Seq(f)) => Seq(f ~ None)
        case f => Seq(f ~ None)
      }
    )

    lazy val termula: Syntax[Termula] = recursive {
      prefixes(binder, iffImpliesTermula)(
        { case (label ~ variable, f) => Termula(label, Seq(Termula(variable, Seq()), f)) },
        { case Termula(label: BinderLabel, Seq(Termula(variable: VariableFormulaLabel, Seq()), f)) =>
          (label ~ variable, f)
        }
      )
    }
    ///////////////////////////////////////////////////////////////////

    val sequent: Syntax[TermulaSequent] = (repsep(termula, semicolon) ~ opt(sequentSymbol.skip ~ repsep(termula, semicolon))).map[TermulaSequent](
      {
        case left ~ Some(right) => TermulaSequent(left.toSet, right.toSet)
        case right ~ None => TermulaSequent(Set(), right.toSet)
      },
      {
        case TermulaSequent(Seq(), right) => Seq(right.toSeq ~ None)
        case TermulaSequent(left, Seq()) => Seq(left.toSeq ~ Some(Seq(False.toTermula)))
        case TermulaSequent(left, right) => Seq(left.toSeq ~ Some(right.toSeq))
      }
    )

    val parser: Parser[TermulaSequent] = Parser(sequent)
    val printer: PrettyPrinter[TermulaSequent] = PrettyPrinter(sequent)

    val termulaParser: SequentParser.Parser[Termula] = Parser(termula)
    val termulaPrinter: SequentParser.PrettyPrinter[Termula] = PrettyPrinter(termula)

    def apply(it: Iterator[Token]): ParseResult[Sequent] = parseSequent(it)

    def unapply(s: Sequent): Option[String] = printSequent(s)

    def parseSequent(it: Iterator[Token]): ParseResult[Sequent] = parser(it).map(_.toSequent)
    def printSequent(s: Sequent): Option[String] = printer(s.toTermulaSequent).map(SequentLexer.unapply)

    def parseFormula(it: Iterator[Token]): ParseResult[Formula] = termulaParser(it).map(_.toFormula)
    def printFormula(f: Formula): Option[String] = termulaPrinter(f.toTermula).map(SequentLexer.unapply)

    def parseTerm(it: Iterator[Token]): ParseResult[Term] = termulaParser(it).map(_.toTerm)

    def printTerm(t: Term): Option[String] = termulaPrinter(t.toTermula).map(SequentLexer.unapply)
  }
}
