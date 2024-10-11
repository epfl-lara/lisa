package lisa.utils.parsing

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SCProofCheckerJudgement.*
import lisa.kernel.proof.SequentCalculus.*

val FOLPrinter = Printer(FOLParser)

/**
 * A set of methods to pretty-print kernel trees.
 */
class Printer(parser: Parser) {

  private def spaceSeparator(compact: Boolean): String = if (compact) "" else " "

  private def commaSeparator(compact: Boolean, symbol: String = ","): String = s"$symbol${spaceSeparator(compact)}"

  /**
   * Returns a string representation of this formula. See also [[prettyTerm]].
   * Example output:
   * <pre>
   * ∀x, y. (∀z. (z ∈ x) ⇔ (z ∈ y)) ⇔ (x = y)
   * </pre>
   *
   * @param formula the formula
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this formula
   */
  def prettyFormula(formula: Formula, compact: Boolean = false): String = parser.printFormula(formula)

  /**
   * Returns a string representation of this term. See also [[prettyFormula]].
   * Example output:
   * <pre>
   * f({w, (x, y)}, z)
   * </pre>
   *
   * @param term    the term
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this term
   */
  def prettyTerm(term: Term, compact: Boolean = false): String = parser.printTerm(term)

  /**
   * Returns a string representation of this sequent.
   * Example output:
   * <pre>
   * ⊢ ∀x, y. (∀z. (z ∈ x) ⇔ (z ∈ y)) ⇔ (x = y)
   * </pre>
   *
   * @param sequent the sequent
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this sequent
   */
  def prettySequent(sequent: Sequent, compact: Boolean = false): String = parser.printSequent(sequent)

  
}
