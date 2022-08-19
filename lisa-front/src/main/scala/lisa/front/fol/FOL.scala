package lisa.front.fol

import lisa.front.fol.conversions.to.*
import lisa.front.fol.conversions.from.*
import lisa.front.fol.definitions.*
import lisa.front.fol.ops.*
import lisa.front.fol.utils.*
import lisa.front.printer.FrontPositionedPrinter

/**
 * The package containing all the definitions and utilities to work with first order logic (FOL).
 */
object FOL extends FormulaDefinitions
  with TermConversionsTo with FormulaConversionsTo
  with TermConversionsFrom with FormulaConversionsFrom
  with TermUtils with FormulaUtils
  with TermOps with FormulaOps {

  override protected def pretty(term: Term): String = FrontPositionedPrinter.prettyTerm(term)
  override protected def pretty(formula: Formula): String = FrontPositionedPrinter.prettyFormula(formula)

  type LabelType = Label
  type SchematicLabelType = SchematicLabel
  type LabeledTreeType[A <: Label] = LabeledTree[A]
  type WithArityType[N <: Arity] = WithArity[N]

}
