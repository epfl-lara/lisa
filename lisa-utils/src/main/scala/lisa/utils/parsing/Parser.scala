package lisa.utils.parsing

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.kernel.fol.FOL.equality
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.KernelHelpers.False
import lisa.utils.KernelHelpers.given_Conversion_Identifier_String
import lisa.utils.KernelHelpers.given_Conversion_String_Identifier
import lisa.utils.parsing.ParsingUtils
import scallion.*
import scallion.util.Unfolds.unfoldRight
import silex.*

import scala.collection.mutable

val FOLParser = Parser(SynonymInfo.empty, "=" :: Nil, Nil)

enum Associativity {
  case Left, Right, None
}

//TODO: Deal with errors in parsing.
class ParsingException(parsedString: String, errorMessage: String) extends lisa.utils.LisaException(errorMessage) {
  def showError: String = ""
}

abstract class ParserException(msg: String) extends Exception(msg)

class UnexpectedInputException(input: String, position: (Int, Int), expected: String)
    extends ParserException(
      s"""
         |$input
         |${" " * position._1 + "^" * (position._2 - position._1)}
         |Unexpected input: expected $expected
         |""".stripMargin
    )

object UnexpectedEndOfInputException extends Exception("Unexpected end of input")

object UnreachableException extends ParserException("Internal error: expected unreachable")

class PrintFailedException(inp: Sequent | Formula | Term) extends ParserException(s"Printing of $inp failed unexpectedly")

/**
 * @param synonymToCanonical information about synonyms that correspond to the same FunctionLabel / AtomicLabel.
 *                           Can be constructed with [[lisa.utils.SynonymInfoBuilder]]
 * @param infixPredicates list of infix predicates' names
 * @param infixFunctions list of infix functions and their associativity in the decreasing order of priority
 */
class Parser(
    synonymToCanonical: SynonymInfo,
    infixPredicates: List[String],
    infixFunctions: List[(String, Associativity)]
) {
  private val infixPredicateSet = infixPredicates.toSet
  private val infixFunctionSet = infixFunctions.map(_._1).toSet
  private val infixSet = infixPredicateSet ++ infixFunctionSet

  /**
   * Parses a sequent from a string. A sequent consists of the left and right side, separated by `⊢` or `|-`.
   * Left and right sides consist of formulas, separated by `;`.
   *
   * @see Parser#parseFormula
   * @param s string representation of the sequent
   * @return parsed sequent on success, throws an exception when unexpected input or end of input.
   */
  def parseSequent(s: String): Sequent =
    try {
      extractParseResult(s, SequentParser.parseTermulaSequent(SequentLexer(s.iterator))).toSequent
    } catch {
      case e: ExpectedFormulaGotTerm => throw new UnexpectedInputException(s, e.range, "formula")
      case e: ExpectedTermGotFormula => throw new UnexpectedInputException(s, e.range, "term")
    }

  /**
   * Parses a formula from a string. A formula can be:
   * <p> - a bound formula: `∀'x. f`, `∃'x. f`, `∃!'x. f`. A binder binds the entire formula until the end of the scope (a closing parenthesis or the end of string).
   * <p> - two formulas, connected by `⇔` or `⇒`. Iff / implies bind less tight than and / or.
   * <p> - a conjunction or disjunction of arbitrary number of formulas. `∧` binds tighter than `∨`.
   * <p> - negated formula.
   * <p> - schematic connector formula: `?c(f1, f2, f3)`.
   * <p> - equality of two formulas: `f1 = f2`.
   * <p> - a constant `p(a)` or schematic `'p(a)` predicate application to arbitrary number of term arguments.
   * <p> - boolean constant: `⊤` or `⊥`.
   *
   * @param s string representation of the formula
   * @return parsed formula on success, throws an exception when unexpected input or end of input.
   */
  def parseFormula(s: String): Formula =
    try {
      extractParseResult(s, SequentParser.parseTermula(SequentLexer(s.iterator))).toFormula
    } catch {
      case e: ExpectedFormulaGotTerm => throw new UnexpectedInputException(s, e.range, "formula")
      case e: ExpectedTermGotFormula => throw new UnexpectedInputException(s, e.range, "term")
    }

  /**
   * Parses a term from a string. A term is a constant `c`, a schematic variable `'x` or an application of a constant `f(a)`
   * or a schematic `'f(a)` function to other terms.
   *
   * @param s string representation of the term
   * @return parsed term on success, throws an exception when unexpected input or end of input.
   */
  def parseTerm(s: String): Term =
    try {
      extractParseResult(s, SequentParser.parseTermula(SequentLexer(s.iterator))).toTerm
    } catch {
      case e: ExpectedFormulaGotTerm => throw new UnexpectedInputException(s, e.range, "formula")
      case e: ExpectedTermGotFormula => throw new UnexpectedInputException(s, e.range, "term")
    }

  private def extractParseResult[T](input: String, r: SequentParser.ParseResult[T]): T = r match {
    case SequentParser.Parsed(value, _) => value
    case SequentParser.UnexpectedToken(token, rest) => throw UnexpectedInputException(input, token.range, "one of " + rest.first.mkString(", "))
    case SequentParser.UnexpectedEnd(_) => throw UnexpectedEndOfInputException
  }

  /**
   * Returns a string representation of the sequent. Empty set of formulas on the left side is not printed.
   * Empty set of formulas on the right side is represented as `⊥` (false).
   *
   * @param s sequent to print
   * @return string representation of the sequent, or the smallest component thereof, on which printing failed
   */
  def printSequent(s: Sequent): String = SequentParser
    .printTermulaSequent(s.toTermulaSequent)
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
    .printTermula(f.toTermula)
    .getOrElse({
      f match {
        case AtomicFormula(_, args) => args.foreach(printTerm)
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
    .printTermula(t.toTermula)
    .getOrElse({
      t match {
        case Term(_, args) => args.foreach(printTerm)
        case VariableTerm(_) => ()
      }
      throw PrintFailedException(t)
    })

  private val UNKNOWN_RANGE = (-1, -1)

  private[Parser] object SequentLexer extends Lexers with CharLexers {
    sealed abstract class FormulaToken(stringRepr: String) {
      def printString: String = stringRepr
      val range: (Int, Int)
    }

    case class ForallToken(range: (Int, Int)) extends FormulaToken(Forall.id)

    case class ExistsOneToken(range: (Int, Int)) extends FormulaToken(ExistsOne.id)

    case class ExistsToken(range: (Int, Int)) extends FormulaToken(Exists.id)

    case class DotToken(range: (Int, Int)) extends FormulaToken(".")

    case class AndToken(range: (Int, Int), prefix: Boolean) extends FormulaToken(And.id)

    case class OrToken(range: (Int, Int), prefix: Boolean) extends FormulaToken(Or.id)

    case class ImpliesToken(range: (Int, Int)) extends FormulaToken(Implies.id)

    case class IffToken(range: (Int, Int)) extends FormulaToken(Iff.id)

    case class NegationToken(range: (Int, Int)) extends FormulaToken(Neg.id)

    case class TrueToken(range: (Int, Int)) extends FormulaToken("⊤")

    case class FalseToken(range: (Int, Int)) extends FormulaToken("⊥")

    // Constant functions and predicates
    case class ConstantToken(id: String, range: (Int, Int)) extends FormulaToken(id)

    // Variables, schematic functions and predicates
    case class SchematicToken(id: String, range: (Int, Int)) extends FormulaToken(schematicSymbol + id)

    // This token is not required for parsing, but is needed to print spaces around infix operations
    case class InfixToken(id: String, range: (Int, Int)) extends FormulaToken(id)

    // Schematic connector (prefix notation is expected)
    case class SchematicConnectorToken(id: String, range: (Int, Int)) extends FormulaToken(schematicConnectorSymbol + id)

    case class ParenthesisToken(isOpen: Boolean, range: (Int, Int)) extends FormulaToken(if (isOpen) "(" else ")")

    case class CommaToken(range: (Int, Int)) extends FormulaToken(",")

    case class SemicolonToken(range: (Int, Int)) extends FormulaToken(";")

    case class SequentToken(range: (Int, Int)) extends FormulaToken("⊢")

    case class SpaceToken(range: (Int, Int)) extends FormulaToken(" ")

    case class UnknownToken(str: String, range: (Int, Int)) extends FormulaToken(str)

    type Token = FormulaToken
    type Position = Int

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
      elem('∀') |> { (_, r) => ForallToken(r) },
      word("∃!") |> { (_, r) => ExistsOneToken(r) },
      elem('∃') |> { (_, r) => ExistsToken(r) },
      elem('.') |> { (_, r) => DotToken(r) },
      elem('∧') | word("/\\") |> { (_, r) => AndToken(r, false) },
      elem('∨') | word("\\/") |> { (_, r) => OrToken(r, false) },
      word(Implies.id.name) | word("=>") | word("==>") | elem('⇒') |> { (_, r) => ImpliesToken(r) },
      word(Iff.id.name) | word("<=>") | word("<==>") | elem('⟷') | elem('⇔') |> { (_, r) => IffToken(r) },
      elem('⊤') | elem('T') | word("True") | word("true") |> { (_, r) => TrueToken(r) },
      elem('⊥') | elem('F') | word("False") | word("false") |> { (_, r) => FalseToken(r) },
      elem('¬') | elem('!') |> { (_, r) => NegationToken(r) },
      elem('(') |> { (_, r) => ParenthesisToken(true, r) },
      elem(')') |> { (_, r) => ParenthesisToken(false, r) },
      elem(',') |> { (_, r) => CommaToken(r) },
      elem(';') |> { (_, r) => SemicolonToken(r) },
      elem('⊢') | word("|-") |> { (_, r) => SequentToken(r) },
      many1(whiteSpace) |> { (_, r) => SpaceToken(r) },
      word(schematicSymbol) ~ variableLike |> { (cs, r) =>
        // drop the '
        SchematicToken(cs.drop(1).mkString, r)
      },
      word(schematicConnectorSymbol) ~ variableLike |> { (cs, r) =>
        SchematicConnectorToken(cs.drop(1).mkString, r)
      },
      // Currently the path is merged into the id on the lexer level. When qualified ids are supported, this should be
      // lifted into the parser.
      opt(path) ~ (variableLike | number | arbitrarySymbol | symbolSequence | escaped) |> { (cs, r) => ConstantToken(cs.filter(_ != escapeChar).mkString, r) }
    ) onError { (cs, r) =>
      UnknownToken(cs.mkString, r)
    }

    def apply(it: Iterator[Char]): Iterator[Token] = {
      val source = Source.fromIterator(it, IndexPositioner)
      lexer
        .spawn(source)
        .map({
          case ConstantToken(id, r) if infixSet.contains(id) => InfixToken(id, r)
          case t => t
        })
        .filter(!_.isInstanceOf[SpaceToken])
    }

    def unapply(tokens: Iterator[Token]): String = {
      val space = " "
      tokens
        .foldLeft(Nil: List[String]) {
          // Sequent token is the only separator that can have an empty left side; in this case, omit the space before
          case (Nil, s: SequentToken) => s.printString :: space :: Nil
          case (l, t) =>
            t match {
              // do not require spaces

              case _: ForallToken | _: ExistsToken | _: ExistsOneToken | _: NegationToken | _: ConstantToken | _: SchematicToken | _: SchematicConnectorToken | _: TrueToken | _: FalseToken |
                  _: ParenthesisToken | _: SpaceToken | AndToken(_, true) | OrToken(_, true) =>
                l :+ t.printString
              // space after: separators
              case _: DotToken | _: CommaToken | _: SemicolonToken => l :+ t.printString :+ space
              // space before and after: infix, connectors, sequent symbol

              case _: InfixToken | _: AndToken | _: OrToken | _: ImpliesToken | _: IffToken | _: SequentToken => l :+ space :+ t.printString :+ space
              case _: UnknownToken => throw UnreachableException
            }
        }
        .mkString
    }
  }

  case class RangedLabel(folLabel: FOL.FormulaLabel, range: (Int, Int))

  abstract class TermulaConversionError(range: (Int, Int)) extends Exception
  case class ExpectedTermGotFormula(range: (Int, Int)) extends TermulaConversionError(range)
  case class ExpectedFormulaGotTerm(range: (Int, Int)) extends TermulaConversionError(range)

  /**
   * Termula represents parser-level union of terms and formulas.
   * After parsing, the termula can be converted either to a term or to a formula:
   * <p> - to be converted to a term, termula must consist only of function applications;
   * <p> - to be converted to a formula, `args` of the termula are interpreted as formulas until a predicate application is observed;
   * `args` of the predicate application are terms.
   *
   * <p> Convention: since the difference between `TermLabel`s and `AtomicLabel`s is purely semantic and Termula needs
   * FormulaLabels (because of connector and binder labels), all TermLabels are translated to the corresponding
   * PredicateLabels (see [[toTermula]]).
   *
   * @param label `AtomicLabel` for predicates and functions, `ConnectorLabel` or `BinderLabel`
   * @param args Predicate / function arguments for `AtomicLabel`, connected formulas for `ConnectorLabel`,
   *             `Seq(VariableFormulaLabel(bound), inner)` for `BinderLabel`
   */
  case class Termula(label: RangedLabel, args: Seq[Termula], range: (Int, Int)) {
    def toTerm: Term = label.folLabel match {
      case _: BinderLabel | _: ConnectorLabel => throw ExpectedTermGotFormula(range)
      case t: ConstantAtomicLabel => Term(ConstantFunctionLabel(t.id, t.arity), args.map(_.toTerm))
      case t: SchematicPredicateLabel => Term(SchematicFunctionLabel(t.id, t.arity), args.map(_.toTerm))
      case v: VariableFormulaLabel => Term(VariableLabel(v.id), Seq())
    }

    def toFormula: Formula = label.folLabel match {
      case p: AtomicLabel => AtomicFormula(p, args.map(_.toTerm))
      case c: ConnectorLabel => ConnectorFormula(c, args.map(_.toFormula))
      case b: BinderLabel =>
        args match {
          case Seq(Termula(RangedLabel(v: VariableFormulaLabel, _), Seq(), _), f) => BinderFormula(b, VariableLabel(v.id), f.toFormula)
          // wrong binder format. Termulas can only be constructed within parser and they are expected to always be constructed according
          // to the format above
          case _ => throw UnreachableException
        }
    }
  }

  extension (f: Formula) {

    def toTermula: Termula = {
      given Conversion[FOL.FormulaLabel, RangedLabel] with {
        def apply(f: FOL.FormulaLabel): RangedLabel = RangedLabel(f, UNKNOWN_RANGE)
      }

      f match {
        case AtomicFormula(label, args) => Termula(label, args.map(_.toTermula), UNKNOWN_RANGE)
        // case ConnectorFormula(And | Or, Seq(singleArg)) => singleArg.toTermula
        case ConnectorFormula(label, args) => Termula(label, args.map(_.toTermula), UNKNOWN_RANGE)
        case BinderFormula(label, bound, inner) => Termula(label, Seq(Termula(VariableFormulaLabel(bound.id), Seq(), UNKNOWN_RANGE), inner.toTermula), UNKNOWN_RANGE)
      }
    }
  }

  extension (t: Term) {
    def toTermula: Termula = {
      given Conversion[FOL.FormulaLabel, RangedLabel] with {
        def apply(f: FOL.FormulaLabel): RangedLabel = RangedLabel(f, UNKNOWN_RANGE)
      }
      val newLabel = t.label match {
        case ConstantFunctionLabel(id, arity) => ConstantAtomicLabel(id, arity)
        case SchematicFunctionLabel(id, arity) => SchematicPredicateLabel(id, arity)
        case VariableLabel(id) => VariableFormulaLabel(id)
      }
      Termula(newLabel, t.args.map(_.toTermula), UNKNOWN_RANGE)
    }
  }

  case class TermulaSequent(left: Set[Termula], right: Set[Termula]) {
    def toSequent: Sequent = Sequent(left.map(_.toFormula), right.map(_.toFormula))
  }

  extension (s: Sequent) {
    def toTermulaSequent: TermulaSequent = TermulaSequent(s.left.map(_.toTermula), s.right.map(_.toTermula))
  }

  private[Parser] object SequentParser extends Parsers with ParsingUtils {
    sealed abstract class TokenKind(debugString: String) {
      override def toString: Mark = debugString
    }
    // and, or are both (left) associative and bind tighter than implies, iff
    case object AndKind extends TokenKind(And.id)
    case object OrKind extends TokenKind(Or.id)
    // implies, iff are both non-associative and are of equal priority, lower than and, or
    case object TopLevelConnectorKind extends TokenKind(s"${Implies.id} or ${Iff.id}")
    case object NegationKind extends TokenKind(Neg.id)
    case object BooleanConstantKind extends TokenKind("boolean constant")
    case object IdKind extends TokenKind("constant or schematic id")
    case class InfixKind(id: String) extends TokenKind(s"infix operation $id")
    case object CommaKind extends TokenKind(",")
    case class ParenthesisKind(isOpen: Boolean) extends TokenKind(if (isOpen) "(" else ")")
    case object BinderKind extends TokenKind("binder")
    case object DotKind extends TokenKind(".")
    case object SemicolonKind extends TokenKind(";")
    case object SequentSymbolKind extends TokenKind("⊢")
    case object OtherKind extends TokenKind("<error>")

    import SequentLexer._
    type Token = FormulaToken
    type Kind = TokenKind

    // can safely skip tokens which were mapped to unit with elem(kind).unit(token)
    import SafeImplicits._

    def getKind(t: Token): Kind = t match {
      case _: AndToken => AndKind
      case _: OrToken => OrKind
      case _: IffToken | _: ImpliesToken => TopLevelConnectorKind
      case _: NegationToken => NegationKind
      case _: TrueToken | _: FalseToken => BooleanConstantKind
      case InfixToken(id, _) => InfixKind(id)
      case _: ConstantToken | _: SchematicToken | _: SchematicConnectorToken => IdKind
      case _: CommaToken => CommaKind
      case ParenthesisToken(isOpen, _) => ParenthesisKind(isOpen)
      case _: ExistsToken | _: ExistsOneToken | _: ForallToken => BinderKind
      case _: DotToken => DotKind
      case _: SemicolonToken => SemicolonKind
      case _: SequentToken => SequentSymbolKind
      case _: SpaceToken | _: UnknownToken => OtherKind
    }

    /////////////////////// SEPARATORS ////////////////////////////////
    def parens(isOpen: Boolean): Syntax[Unit] =
      elem(ParenthesisKind(isOpen)).unit(ParenthesisToken(isOpen, UNKNOWN_RANGE))

    val open: Syntax[Unit] = parens(true)

    val closed: Syntax[Unit] = parens(false)

    val comma: Syntax[Unit] = elem(CommaKind).unit(CommaToken(UNKNOWN_RANGE))

    val dot: Syntax[Unit] = elem(DotKind).unit(DotToken(UNKNOWN_RANGE))

    val semicolon: Syntax[Unit] = elem(SemicolonKind).unit(SemicolonToken(UNKNOWN_RANGE))

    val sequentSymbol: Syntax[Unit] = elem(SequentSymbolKind).unit(SequentToken(UNKNOWN_RANGE))
    ///////////////////////////////////////////////////////////////////

    //////////////////////// LABELS ///////////////////////////////////
    val toplevelConnector: Syntax[RangedLabel] = accept(TopLevelConnectorKind)(
      {
        case ImpliesToken(r) => RangedLabel(Implies, r)
        case IffToken(r) => RangedLabel(Iff, r)
      },
      {
        case RangedLabel(Implies, r) => Seq(ImpliesToken(r))
        case RangedLabel(Iff, r) => Seq(IffToken(r))
        case _ => throw UnreachableException
      }
    )

    val negation: Syntax[RangedLabel] = accept(NegationKind)(
      { case NegationToken(r) => RangedLabel(Neg, r) },
      {
        case RangedLabel(Neg, r) => Seq(NegationToken(r))
        case _ => throw UnreachableException
      }
    )

    val INFIX_ARITY = 2
    ///////////////////////////////////////////////////////////////////

    //////////////////////// TERMULAS /////////////////////////////////
    // can appear without parentheses
    lazy val simpleTermula: Syntax[Termula] = prefixApplication | negated | bool
    lazy val subtermula: Syntax[Termula] = simpleTermula | open.skip ~ termula ~ closed.skip

    val bool: Syntax[Termula] = accept(BooleanConstantKind)(
      {
        case TrueToken(r) => Termula(RangedLabel(top, r), Seq(), r)
        case FalseToken(r) => Termula(RangedLabel(bot, r), Seq(), r)
      },
      {
        case Termula(RangedLabel(And, _), Seq(), r) => Seq(TrueToken(r))
        case Termula(RangedLabel(Or, _), Seq(), r) => Seq(FalseToken(r))
        case _ => throw UnreachableException
      }
    )

    case class RangedTermulaSeq(ts: Seq[Termula], range: (Int, Int))
    lazy val args: Syntax[RangedTermulaSeq] = recursive(
      (elem(ParenthesisKind(true)) ~ repsep(termula, comma) ~ elem(ParenthesisKind(false))).map(
        { case start ~ ts ~ end =>
          RangedTermulaSeq(ts, (start.range._1, end.range._2))
        },
        { case RangedTermulaSeq(ts, (start, end)) =>
          Seq(ParenthesisToken(true, (start, start)) ~ ts ~ ParenthesisToken(false, (end, end)))
        }
      )
    )

    def reconstructPrefixApplication(t: Termula): Token ~ Option[RangedTermulaSeq] = {
      val argsRange = (t.label.range._2 + 1, t.range._2)
      t.label.folLabel match {
        case VariableFormulaLabel(id) => SchematicToken(id, t.label.range) ~ None
        case SchematicPredicateLabel(id, _) => SchematicToken(id, t.range) ~ Some(RangedTermulaSeq(t.args, argsRange))
        case ConstantAtomicLabel(id, arity) =>
          ConstantToken(synonymToCanonical.getPrintName(id), t.label.range) ~
            (if (arity == 0) None else Some(RangedTermulaSeq(t.args, argsRange)))
        case _ => throw UnreachableException
      }
    }

    // schematic connector, function, or predicate; constant function or predicate
    val prefixApplication: Syntax[Termula] = ((elem(IdKind) | elem(OrKind) | elem(AndKind)) ~ opt(args)).map(
      { case p ~ optArgs =>
        val args: Seq[Termula] = optArgs.map(_.ts).getOrElse(Seq())
        val l = p match {

          case ConstantToken(id, _) => ConstantAtomicLabel(synonymToCanonical.getInternalName(id), args.size)
          case SchematicToken(id, _) =>
            if (args.isEmpty) VariableFormulaLabel(id) else SchematicPredicateLabel(id, args.size)
          case SchematicConnectorToken(id, _) => SchematicConnectorLabel(id, args.size)
          case AndToken(_, _) => And
          case OrToken(_, _) => Or
          case _ => throw UnreachableException
        }
        Termula(RangedLabel(l, p.range), args, (p.range._1, optArgs.map(_.range._2).getOrElse(p.range._2)))
      },
      {
        case t @ Termula(RangedLabel(_: AtomicLabel, _), _, _) => Seq(reconstructPrefixApplication(t))
        case t @ Termula(RangedLabel(SchematicConnectorLabel(id, _), r), args, _) =>
          val argsRange = (t.label.range._2 + 1, t.range._2)
          Seq(SchematicConnectorToken(id, r) ~ Some(RangedTermulaSeq(args, argsRange)))
        case t @ Termula(RangedLabel(And, r), args, _) =>
          val argsRange = (t.label.range._2 + 1, t.range._2)
          Seq(AndToken(r, true) ~ Some(RangedTermulaSeq(args, argsRange)))
        case t @ Termula(RangedLabel(Or, r), args, _) =>
          val argsRange = (t.label.range._2 + 1, t.range._2)
          Seq(OrToken(r, true) ~ Some(RangedTermulaSeq(args, argsRange)))

        case _ => throw UnreachableException
      }
    )

    val infixFunctionLabels: List[PrecedenceLevel[RangedLabel]] = infixFunctions.map({ case (l, assoc) =>
      elem(InfixKind(l)).map[RangedLabel](
        {
          case InfixToken(`l`, range) => RangedLabel(ConstantAtomicLabel(synonymToCanonical.getInternalName(l), INFIX_ARITY), range)
          case _ => throw UnreachableException
        },
        {
          case RangedLabel(ConstantAtomicLabel(id, INFIX_ARITY), range) => Seq(InfixToken(synonymToCanonical.getPrintName(id), range))
          case _ => throw UnreachableException
        }
      ) has assoc
    })

    val infixPredicateLabels: List[PrecedenceLevel[RangedLabel]] = infixPredicates.map(l =>
      elem(InfixKind(l)).map[RangedLabel](
        {
          case InfixToken(`l`, range) => RangedLabel(ConstantAtomicLabel(synonymToCanonical.getInternalName(l), INFIX_ARITY), range)
          case _ => throw UnreachableException
        },
        {
          case RangedLabel(ConstantAtomicLabel(id, INFIX_ARITY), range) => Seq(InfixToken(synonymToCanonical.getPrintName(id), range))
          case _ => throw UnreachableException
        }
      ) has Associativity.None
    )

    val negated: Syntax[Termula] = recursive {
      (negation ~ subtermula).map(
        { case n ~ f =>
          Termula(n, Seq(f), (n.range._1, f.range._2))
        },
        {
          case Termula(l @ RangedLabel(Neg, _), Seq(f), _) => Seq(l ~ f)
          case _ => throw UnreachableException
        }
      )
    }

    val and: Syntax[RangedLabel] = elem(AndKind).map[RangedLabel](
      {

        case AndToken(r, _) => RangedLabel(And, r)
        case _ => throw UnreachableException
      },
      {
        case RangedLabel(And, r) => Seq(AndToken(r, false))
        case _ => throw UnreachableException
      }
    )

    val or: Syntax[RangedLabel] = elem(OrKind).map[RangedLabel](
      {
        case OrToken(r, _) => RangedLabel(Or, r)
        case _ => throw UnreachableException
      },
      {
        case RangedLabel(Or, r) => Seq(OrToken(r, false))
        case _ => throw UnreachableException
      }
    )

    // 'and' has higher priority than 'or'
    val connectorTermula: Syntax[Termula] = infixOperators[RangedLabel, Termula](subtermula)(
      infixFunctionLabels ++
        infixPredicateLabels ++
        ((and has Associativity.Left) ::
          (or has Associativity.Left) ::
          (toplevelConnector has Associativity.None) :: Nil)*
    )(
      (l, conn, r) => Termula(conn, Seq(l, r), (l.range._1, r.range._2)),
      {
        case Termula(pred @ RangedLabel(ConstantAtomicLabel(_, INFIX_ARITY), _), Seq(l, r), _) => (l, pred, r)
        case Termula(conn @ RangedLabel(_: ConnectorLabel, _), Seq(l, r), _) =>
          (l, conn, r)
        case Termula(conn @ RangedLabel(_: ConnectorLabel, _), l +: rest, _) if rest.nonEmpty =>
          val last = rest.last
          val leftSide = rest.dropRight(1)
          // parser only knows about connector formulas of two arguments, so we unfold the formula of many arguments to
          // multiple nested formulas of two arguments
          (leftSide.foldLeft(l)((f1, f2) => Termula(conn, Seq(f1, f2), UNKNOWN_RANGE)), conn, last)
      }
    )

    val binderLabel: Syntax[RangedLabel] = accept(BinderKind)(
      {
        case ExistsToken(r) => RangedLabel(Exists, r)
        case ExistsOneToken(r) => RangedLabel(ExistsOne, r)
        case ForallToken(r) => RangedLabel(Forall, r)
      },
      {
        case RangedLabel(Exists, r) => Seq(ExistsToken(r))
        case RangedLabel(ExistsOne, r) => Seq(ExistsOneToken(r))
        case RangedLabel(Forall, r) => Seq(ForallToken(r))
        case _ => throw UnreachableException
      }
    )

    val boundVariable: Syntax[RangedLabel] = accept(IdKind)(
      t => {
        val (id, r) = t match {
          case ConstantToken(id, r) => (id, r)
          case SchematicToken(id, r) => (id, r)
        }
        RangedLabel(VariableFormulaLabel(id), r)
      },
      {
        case RangedLabel(VariableFormulaLabel(id), r) => Seq(SchematicToken(id, r))
        case _ => throw UnreachableException
      }
    )

    val binder: Syntax[RangedLabel ~ RangedLabel] = binderLabel ~ boundVariable ~ dot.skip

    lazy val termula: Syntax[Termula] = recursive {
      prefixes(binder, connectorTermula)(
        { case (label ~ variable, f) => Termula(label, Seq(Termula(variable, Seq(), variable.range), f), (label.range._1, f.range._2)) },
        { case Termula(label @ RangedLabel(_: BinderLabel, _), Seq(Termula(variable @ RangedLabel(_: VariableFormulaLabel, _), Seq(), _), f), _) =>
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

    def parseTermulaSequent(it: Iterator[Token]): ParseResult[TermulaSequent] = parser(it)
    def printTermulaSequent(s: TermulaSequent): Option[String] = printer(s).map(SequentLexer.unapply)

    def parseTermula(it: Iterator[Token]): ParseResult[Termula] = termulaParser(it)
    def printTermula(t: Termula): Option[String] = termulaPrinter(t).map(SequentLexer.unapply)
  }
}
