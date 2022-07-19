package lisa.kernel.fol

/**
 * Definitions of terms; depends on [[TermLabelDefinitions]].
 */
private[fol] trait TermDefinitions extends TermLabelDefinitions {

  protected trait TreeWithLabel[A] {
    val label: A

    /**
     * @return The list of free variables in the term
     */
    def freeVariables: Set[VariableLabel]

    /**
     * @return The list of constant (i.e. non schematic) function symbols, including of arity 0.
     */
    def constantFunctions: Set[ConstantFunctionLabel]

    /**
     * @return The list of schematic function symbols (including free variables) in the term
     */
    def schematicTerms: Set[SchematicTermLabel]
  }

  /**
   * The parent classes of terms.
   * A term is a tree with nodes labeled by functions labels or variables.
   * The number of children of a node is restricted by the arity imposed by the label.
   */
  sealed abstract class Term extends TreeWithLabel[TermLabel]

  /**
   * A term which consists of a single variable.
   *
   * @param label The label of the variable.
   */
  sealed case class VariableTerm(label: VariableLabel) extends Term {
    override def freeVariables: Set[VariableLabel] = Set(label)

    override def constantFunctions: Set[ConstantFunctionLabel] = Set.empty
    override def schematicTerms: Set[SchematicTermLabel] = Set(label)
  }

  /**
   * A term labelled by a function symbol. It must contain a number of children equal to the arity of the symbol
   *
   * @param label The label of the node
   * @param args  children of the node. The number of argument must be equal to the arity of the function.
   */
  sealed case class FunctionTerm(label: FunctionLabel, args: Seq[Term]) extends Term {
    require(label.arity == args.size)

    override def freeVariables: Set[VariableLabel] = args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)

    override def constantFunctions: Set[ConstantFunctionLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions) + l
      case l: SchematicFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions)
    }
    override def schematicTerms: Set[SchematicTermLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTerms)
      case l: SchematicFunctionLabel => args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTerms) + l
    }

    val arity: Int = args.size
  }

}
