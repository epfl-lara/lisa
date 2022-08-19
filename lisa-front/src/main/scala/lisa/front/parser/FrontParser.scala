package lisa.front.parser

import lisa.front.parser.FrontReadingException.ParsingException
import lisa.front.parser.FrontToken
import lisa.front.parser.FrontToken.*
import lisa.front.parser.FrontParsed
import lisa.front.parser.FrontParsed.*

import scala.util.parsing.combinator.Parsers

/**
 * The parser convert low-level tokens into the [[FrontParsed]] intermediate representation.
 */
private[parser] object FrontParser extends Parsers {

  override type Elem = FrontToken

  private def identifier: Parser[Identifier] =
    positioned(accept("identifier", { case id: Identifier => id }))
  private def schematicIdentifier: Parser[SchematicIdentifier] =
    positioned(accept("schematic identifier", { case id: SchematicIdentifier => id }))
  private def schematicConnectorIdentifier: Parser[SchematicConnectorIdentifier] =
    positioned(accept("schematic connector identifier", { case id: SchematicConnectorIdentifier => id }))

  private def integerLiteral: Parser[IntegerLiteral] =
    positioned(accept("integer literal", { case lit: IntegerLiteral => lit }))
  private def ruleName: Parser[RuleName] =
    positioned(accept("rule", { case rule: RuleName => rule }))

  private def indentation: Parser[Indentation] =
    positioned(accept("indentation", { case indentation: Indentation => indentation }))
  private def newLine: Parser[NewLine] =
    positioned(accept("new line", { case line: NewLine => line }))

  private def identifierOrSchematic: Parser[Identifier | SchematicIdentifier | SchematicConnectorIdentifier] =
    positioned((identifier: Parser[Identifier | SchematicIdentifier | SchematicConnectorIdentifier]) | schematicIdentifier | schematicConnectorIdentifier)

  private def binder: Parser[ParsedTermOrFormula] = positioned(
    (Forall() ^^^ ParsedForall.apply | Exists() ^^^ ParsedExists.apply | ExistsOne() ^^^ ParsedExistsOne.apply) ~
      rep1sep(identifier, Comma()) ~ Dot() ~ termOrFormula ^^ { case f ~ bs ~ _ ~ t => f(bs.map(_.identifier), t) }
  )

  private def termOrFormula: Parser[ParsedTermOrFormula] = positioned(termOrFormulaIff)

  private def termOrFormulaIff: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaImplies ~ rep(Iff() ~> termOrFormulaImplies) ^^ { case h ~ t => (h +: t).reduceRight(ParsedIff.apply) })
  private def termOrFormulaImplies: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaOr ~ rep(Implies() ~> termOrFormulaOr) ^^ { case h ~ t => (h +: t).reduceRight(ParsedImplies.apply) })
  private def termOrFormulaOr: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaAnd ~ rep(Or() ~> termOrFormulaAnd) ^^ { case h ~ t => (h +: t).reduceRight(ParsedOr.apply) })
  private def termOrFormulaAnd: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaPredicate ~ rep(And() ~> termOrFormulaPredicate) ^^ { case h ~ t => (h +: t).reduceRight(ParsedAnd.apply) })
  private def termOrFormulaPredicate: Parser[ParsedTermOrFormula] =
    positioned(termNotBinder ~
      rep((Membership() ^^^ ParsedMembership.apply | Subset() ^^^ ParsedSubset.apply | SameCardinality() ^^^ ParsedSameCardinality.apply | Equal() ^^^ ParsedEqual.apply) ~
        termNotBinder) ^^ {
      case t1 ~ ts => ts.foldRight(t1) { case (f ~ tr, tl) => f(tl, tr) }
    })

  private def termNotBinder: Parser[ParsedTermOrFormula] =
    positioned(
      atom
        | Not() ~> atom ^^ ParsedNot.apply
        | binder
    )

  private def atom: Parser[ParsedTermOrFormula] = positioned(
    (Identifier("P") ^^^ ParsedPower.apply | Identifier("U") ^^^ ParsedUnion.apply) ~ ParenthesisOpen() ~ termOrFormula ~ ParenthesisClose() ^^ {
      case f ~ _ ~ t ~ _ => f(t)
    }
      | identifierOrSchematic ~ (ParenthesisOpen() ~> rep1sep(termOrFormula, Comma()) <~ ParenthesisClose()).? ^^ {
      case v ~ argsOpt =>
        val name = v match {
          case Identifier(identifier) => ParsedConstant(identifier)
          case SchematicIdentifier(identifier) => ParsedSchema(identifier, connector = false)
          case SchematicConnectorIdentifier(identifier) => ParsedSchema(identifier, connector = true)
        }
        argsOpt.map(ParsedApplication(name, _)).getOrElse(name)
      }
      | ParenthesisOpen() ~ termOrFormula ~ (Comma() ~> termOrFormula <~ ParenthesisClose()).? ~ ParenthesisClose() ^^ { case _ ~ t1 ~ opt ~ _ => opt match {
      case Some(t2) => ParsedOrderedPair(t1, t2)
      case None => t1
    } }
      | CurlyBracketOpen() ~> (termOrFormula ~ (Comma() ~> termOrFormula).?).? <~ CurlyBracketClose() ^^ {
      case Some(t1 ~ opt2) =>
        opt2 match {
          case Some(t2) => ParsedSet2(t1, t2)
          case None => ParsedSet1(t1)
        }
      case None => ParsedSet0()
    }
      | EmptySet() ^^^ ParsedSet0()
  )

  private def localBinder: Parser[Seq[String]] =
    LocalBinder() ~> rep1sep(identifier, Comma()) <~ Dot() ^^ (fv => fv.map(_.identifier))
  private def localBinderOptional: Parser[Seq[String]] = localBinder.? ^^ (fv => fv.getOrElse(Seq.empty))

  private def topTermOrFormula: Parser[ParsedTopTermOrFormula] =
    localBinderOptional ~ termOrFormula ^^ { case fv ~ t => ParsedTopTermOrFormula(fv, t) }

  private def termOrFormulaSequence: Parser[Seq[ParsedTermOrFormula]] =
    repsep(termOrFormula, Semicolon())

  private def sequent: Parser[ParsedSequent] =
    positioned(localBinderOptional ~ termOrFormulaSequence ~ Turnstile() ~ termOrFormulaSequence ^^ { case fv ~ l ~ _ ~ r => ParsedSequent(fv, l, r) })

  private def partialSequent: Parser[ParsedPartialSequent] =
    positioned(localBinderOptional ~ (
      ((Ellipsis() ~> (Semicolon() ~> rep1sep(termOrFormula, Semicolon())).?) ^^ (opt => (opt.getOrElse(Seq.empty), true))) |
        termOrFormulaSequence ^^ (seq => (seq, false))
      ) ~ Turnstile() ~
      ((Ellipsis() ^^^ Seq.empty | (rep1sep(termOrFormula, Semicolon()) <~ (Semicolon() ~ Ellipsis()))) ^^ (seq => (seq, true)) |
        termOrFormulaSequence ^^ (seq => (seq, false))
      ) ^^ {
        case fv ~ (l, pl) ~ _ ~ (r, pr) => ParsedPartialSequent(fv, l, r, pl, pr)
    })


  private def proofStepParameters: Parser[Seq[ParsedTopTermOrFormula]] =
    SquareBracketOpen() ~> repsep(topTermOrFormula, Semicolon()) <~ SquareBracketClose() ^^ (_.toSeq)

  private def proofStep: Parser[ParsedProofStep] = positioned(
    indentation ~ integerLiteral ~ ruleName ~ repsep(integerLiteral, Comma()) ~ sequent ~ proofStepParameters.? ^^ {
      case i ~ l ~ r ~ p ~ s ~ ps => ParsedProofStep(l.pos, i.spaces, l.value, r.name, p.map(_.value), s, ps.getOrElse(Seq.empty))
    }
  )

  private def proof: Parser[ParsedProof] = positioned(
    (indentation ~ newLine).* ~> rep1sep(proofStep, newLine) <~ (newLine ~ indentation).* ^^ (steps => ParsedProof(steps.toIndexedSeq))
  )


  private def parse[T](parser: Parser[T])(tokens: Seq[FrontToken]): T = {
    val reader = new FrontTokensReader(tokens)
    parser(reader) match {
      case e @ NoSuccess(msg, next) => throw ParsingException(msg, next.pos)
      case Success(result, next) => result
      case e => throw new MatchError(e)
    }
  }

  def parseTermOrFormula(tokens: Seq[FrontToken]): ParsedTermOrFormula =
    parse(positioned(termOrFormula <~ End()))(tokens)

  def parseTopTermOrFormula(tokens: Seq[FrontToken]): ParsedTopTermOrFormula =
    parse(positioned(topTermOrFormula <~ End()))(tokens)

  def parseSequent(tokens: Seq[FrontToken]): ParsedSequent =
    parse(positioned(sequent <~ End()))(tokens)

  def parsePartialSequent(tokens: Seq[FrontToken]): ParsedPartialSequent =
    parse(positioned(partialSequent <~ End()))(tokens)

  def parseProof(tokens: Seq[FrontToken]): ParsedProof =
    parse(positioned(proof <~ End()))(tokens)
}
