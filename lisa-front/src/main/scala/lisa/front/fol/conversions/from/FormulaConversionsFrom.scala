package lisa.front.fol.conversions.from

import lisa.front.fol.conversions.FrontKernelMappings
import lisa.front.fol.definitions.FormulaDefinitions

trait FormulaConversionsFrom extends FormulaDefinitions with TermConversionsFrom with FrontKernelMappings {

  def fromKernel(label: lisa.kernel.fol.FOL.ConstantPredicateLabel): ConstantPredicateLabel[?] =
    predicatesFrom.getOrElse(label, ConstantPredicateLabel.unsafe(label.id, label.arity))
  def fromKernel(label: lisa.kernel.fol.FOL.SchematicPredicateLabel): SchematicPredicateLabel[?] =
    SchematicPredicateLabel.unsafe(label.id, label.arity)
  def fromKernel(label: lisa.kernel.fol.FOL.VariableFormulaLabel): SchematicPredicateLabel[?] =
    SchematicPredicateLabel.unsafe(label.id, 0)
  /**
   * Lifts a predicate label from the kernel to the front.
   * @param label the label in the kernel
   * @return the label in the front
   */
  def fromKernel(label: lisa.kernel.fol.FOL.PredicateLabel): PredicateLabel[?] = label match {
    case schem: lisa.kernel.fol.FOL.SchematicPredicateLabel => fromKernel(schem)
    case constant: lisa.kernel.fol.FOL.ConstantPredicateLabel => fromKernel(constant)
    case variable: lisa.kernel.fol.FOL.VariableFormulaLabel => fromKernel(variable)
  }

  /**
   * Lifts a connector label from the kernel to the front.
   * @param label the label in the kernel
   * @return the label in the front
   */
  def fromKernel(label: lisa.kernel.fol.FOL.ConnectorLabel): ConstantConnectorLabel[?] = connectorsFrom(label)

  /**
   * Lifts a formula from the kernel to the front.
   * @param formula the formula in the kernel
   * @return the formula in the front
   */
  def fromKernel(formula: lisa.kernel.fol.FOL.Formula): Formula = formula match {
    case lisa.kernel.fol.FOL.PredicateFormula(label, args) => PredicateFormula.unsafe(fromKernel(label), args.map(fromKernel))
    case lisa.kernel.fol.FOL.ConnectorFormula(label, args) => ConnectorFormula.unsafe(fromKernel(label), args.map(fromKernel))
    case lisa.kernel.fol.FOL.BinderFormula(label, bound, inner) => BinderFormula(bindersFrom(label), VariableLabel(bound.id), fromKernel(inner))
  }
}
