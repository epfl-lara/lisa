package lisa.front.fol.conversions.to

import lisa.front.fol.definitions.TermDefinitions

trait TermConversionsTo extends TermDefinitions {


  def toKernel(label: ConstantFunctionLabel[?]): lisa.kernel.fol.FOL.ConstantFunctionLabel =
    lisa.kernel.fol.FOL.ConstantFunctionLabel(label.id, label.arity)

  def toKernel(label: SchematicTermLabel[?]): lisa.kernel.fol.FOL.SchematicTermLabel = {
    if (label.arity == 0) lisa.kernel.fol.FOL.VariableLabel(label.id)
    else lisa.kernel.fol.FOL.SchematicFunctionLabel(label.id, label.arity)
  }

  def toKernel(label: SchematicTermLabel[0]): lisa.kernel.fol.FOL.VariableLabel = {
    lisa.kernel.fol.FOL.VariableLabel(label.id)
  }

  /**
   * Translates a label from the front to the kernel.
   * @param label the label in the front
   * @return the label in the kernel
   */
  def toKernel(label: TermLabel[?]): lisa.kernel.fol.FOL.TermLabel = label match {
    case label: ConstantFunctionLabel[?] => toKernel(label)
    case label: SchematicTermLabel[?] => toKernel(label)
  }

  /**
   * Translates a term from the front to the kernel.
   * @param term the term in the front
   * @return the term in the kernel
   */
  def toKernel(term: Term): lisa.kernel.fol.FOL.Term =
    lisa.kernel.fol.FOL.Term(toKernel(term.label), term.args.map(toKernel))


  given Conversion[VariableLabel, lisa.kernel.fol.FOL.VariableLabel] = toKernel
  given Conversion[ConstantFunctionLabel[?], lisa.kernel.fol.FOL.ConstantFunctionLabel] = toKernel
  given Conversion[SchematicTermLabel[?], lisa.kernel.fol.FOL.SchematicTermLabel] = toKernel
  given Conversion[TermLabel[?], lisa.kernel.fol.FOL.TermLabel] = toKernel
  given Conversion[Term, lisa.kernel.fol.FOL.Term] = toKernel

  given Conversion[(Term, Term), (lisa.kernel.fol.FOL.Term, lisa.kernel.fol.FOL.Term)] = (a, b) => (a, b)

}
