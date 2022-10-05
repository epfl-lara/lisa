package lisa.front.fol.conversions.to

import lisa.front.fol.conversions.FrontKernelMappings
import lisa.front.fol.definitions.FormulaDefinitions

trait FormulaConversionsTo extends FormulaDefinitions with TermConversionsTo with FrontKernelMappings {

  def toKernel(label: ConstantConnectorLabel[?]): lisa.kernel.fol.FOL.ConnectorLabel = connectorsTo(label)

  def toKernel(label: ConnectorLabel[?]): lisa.kernel.fol.FOL.ConnectorLabel = label match {
    case constant: ConstantConnectorLabel[?] => toKernel(constant)
    case _: SchematicConnectorLabel[?] => throw new UnsupportedOperationException
  }

  def toKernel(label: ConstantPredicateLabel[?]): lisa.kernel.fol.FOL.ConstantPredicateLabel =
    predicatesTo.getOrElse(label, lisa.kernel.fol.FOL.ConstantPredicateLabel(label.id, label.arity))

  def toKernel(label: SchematicPredicateLabel[0]): lisa.kernel.fol.FOL.VariableFormulaLabel = {
    lisa.kernel.fol.FOL.VariableFormulaLabel(label.id)
  }

  def toKernel(label: SchematicPredicateLabel[?]): lisa.kernel.fol.FOL.SchematicVarOrPredLabel = {
    if (label.arity == 0) lisa.kernel.fol.FOL.VariableFormulaLabel(label.id)
    else lisa.kernel.fol.FOL.SchematicPredicateLabel(label.id, label.arity)
  }

  def toKernel(label: PredicateLabel[?]): lisa.kernel.fol.FOL.PredicateLabel = label match {
    case constant: ConstantPredicateLabel[?] => toKernel(constant)
    case schematic: SchematicPredicateLabel[?] => toKernel(schematic)
  }

  def toKernel(label: BinderLabel): lisa.kernel.fol.FOL.BinderLabel = bindersTo(label)

  /**
   * Translates a label from the front to the kernel.
   * @param label the label in the front
   * @return the label in the kernel
   */
  def toKernel(label: FormulaLabel): lisa.kernel.fol.FOL.FormulaLabel = label match {
    case predicate: PredicateLabel[?] => toKernel(predicate)
    case connector: ConnectorLabel[?] => toKernel(connector)
    case binder: BinderLabel => toKernel(binder)
  }

  def toKernel(formula: PredicateFormula): lisa.kernel.fol.FOL.PredicateFormula =
    lisa.kernel.fol.FOL.PredicateFormula(toKernel(formula.label), formula.args.map(toKernel))

  def toKernel(formula: ConnectorFormula): lisa.kernel.fol.FOL.ConnectorFormula =
    lisa.kernel.fol.FOL.ConnectorFormula(toKernel(formula.label), formula.args.map(toKernel))

  def toKernel(formula: BinderFormula): lisa.kernel.fol.FOL.BinderFormula =
    lisa.kernel.fol.FOL.BinderFormula(toKernel(formula.label), toKernel(formula.bound), toKernel(formula.inner))

  /**
   * Translates a formula from the front to the kernel.
   * @param formula the formula in the front
   * @return the formula in the kernel
   */
  def toKernel(formula: Formula): lisa.kernel.fol.FOL.Formula = formula match {
    case predicate: PredicateFormula => toKernel(predicate)
    case connector: ConnectorFormula => toKernel(connector)
    case binder: BinderFormula => toKernel(binder)
  }

  given Conversion[PredicateFormula, lisa.kernel.fol.FOL.PredicateFormula] = toKernel
  given Conversion[ConnectorFormula, lisa.kernel.fol.FOL.ConnectorFormula] = toKernel
  given Conversion[BinderFormula, lisa.kernel.fol.FOL.BinderFormula] = toKernel
  given Conversion[Formula, lisa.kernel.fol.FOL.Formula] = toKernel
  given Conversion[ConstantPredicateLabel[?], lisa.kernel.fol.FOL.ConstantPredicateLabel] = toKernel
  given Conversion[SchematicPredicateLabel[0], lisa.kernel.fol.FOL.VariableFormulaLabel] = toKernel
  given Conversion[SchematicPredicateLabel[?], lisa.kernel.fol.FOL.SchematicFormulaLabel] = toKernel
  given Conversion[PredicateLabel[?], lisa.kernel.fol.FOL.PredicateLabel] = toKernel
  given Conversion[ConnectorLabel[?], lisa.kernel.fol.FOL.ConnectorLabel] = toKernel
  given Conversion[BinderLabel, lisa.kernel.fol.FOL.BinderLabel] = toKernel
  given Conversion[FormulaLabel, lisa.kernel.fol.FOL.FormulaLabel] = toKernel

  given Conversion[(Formula, Formula), (lisa.kernel.fol.FOL.Formula, lisa.kernel.fol.FOL.Formula)] = (a, b) => (a, b)

}
