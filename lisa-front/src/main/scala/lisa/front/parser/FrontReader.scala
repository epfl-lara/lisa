package lisa.front.parser

import lisa.front.parser.FrontResolver
import lisa.front.fol.FOL.*
import lisa.front.proof.Proof.*

/**
 * The reading API; parses string into first order logic or sequent elements.
 * Reading exceptions can be found in [[FrontReadingException]].
 */
object FrontReader {

  private def lexing(str: String, ascii: Boolean, multiline: Boolean): Seq[FrontToken] = {
    val lexer = if(ascii) FrontLexer.lexingAscii else FrontLexer.lexingUnicode
    lexer(str, !multiline, false)
  }

  def readTerm(str: String, ascii: Boolean = true, toplevel: Boolean = true, multiline: Boolean = false): Term = {
    val tokens = lexing(str, ascii, multiline)
    if(toplevel)
      FrontResolver.resolveTerm(FrontParser.parseTopTermOrFormula(tokens))
    else
      FrontResolver.resolveTerm(FrontParser.parseTermOrFormula(tokens))
  }

  def readFormula(str: String, ascii: Boolean = true, toplevel: Boolean = true, multiline: Boolean = false): Formula = {
    val tokens = lexing(str, ascii, multiline)
    if(toplevel)
      FrontResolver.resolveFormula(FrontParser.parseTopTermOrFormula(tokens))
    else
      FrontResolver.resolveFormula(FrontParser.parseTermOrFormula(tokens))
  }

  def readSequent(str: String, ascii: Boolean = true, multiline: Boolean = false): Sequent =
    FrontResolver.resolveSequent(FrontParser.parseSequent(lexing(str, ascii, multiline)))

  def readPartialSequent(str: String, ascii: Boolean = true, multiline: Boolean = false): PartialSequent =
    FrontResolver.resolvePartialSequent(FrontParser.parsePartialSequent(lexing(str, ascii, multiline)))

}
