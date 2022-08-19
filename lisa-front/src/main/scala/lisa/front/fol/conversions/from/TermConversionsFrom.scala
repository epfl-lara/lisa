package lisa.front.fol.conversions.from

import lisa.front.fol.definitions.TermDefinitions

trait TermConversionsFrom extends TermDefinitions {

  def fromKernel(label: lisa.kernel.fol.FOL.ConstantFunctionLabel): ConstantFunctionLabel[?] =
    ConstantFunctionLabel.unsafe(label.id, label.arity)
  def fromKernel(label: lisa.kernel.fol.FOL.SchematicTermLabel): SchematicTermLabel[?] =
    SchematicTermLabel.unsafe(label.id, label.arity)
  /**
   * Lifts a function label from the kernel to the front.
   * @param label the label in the kernel
   * @return the label in the front
   */
  def fromKernel(label: lisa.kernel.fol.FOL.TermLabel): TermLabel[?] = label match {
    case constant: lisa.kernel.fol.FOL.ConstantFunctionLabel => fromKernel(constant)
    case schematic: lisa.kernel.fol.FOL.SchematicTermLabel => fromKernel(schematic)
  }

  /**
   * Lifts a term from the kernel to the front.
   * @param term the term in the kernel
   * @return the term in the front
   */
  def fromKernel(term: lisa.kernel.fol.FOL.Term): Term = term match {
    case lisa.kernel.fol.FOL.VariableTerm(label) => VariableTerm(VariableLabel(label.id))
    case lisa.kernel.fol.FOL.Term(label, args) => Term.unsafe(fromKernel(label), args.map(fromKernel))
  }
}
