package lisa.kernel.fol

/**
 * Definitions of terms; depends on [[TermLabelDefinitions]].
 */
private[fol] trait TermDefinitions extends TermLabelDefinitions {

  protected trait TreeWithLabel[A] {
    val label: A

    def freeVariables: Set[VariableLabel]

    def constantFunctions: Set[ConstantFunctionLabel]
    def schematicFunctions: Set[SchematicFunctionLabel]
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
  final case class VariableTerm(label: VariableLabel) extends Term {
    override def freeVariables: Set[VariableLabel] = Set(label)

    override def constantFunctions: Set[ConstantFunctionLabel] = Set.empty
    override def schematicFunctions: Set[SchematicFunctionLabel] = Set.empty
  }

  /**
   * A term labelled by a function symbol. It must contain a number of children equal to the arity of the symbol
   *
   * @param label The label of the node
   * @param args  children of the node. The number of argument must be equal to the arity of the function.
   */
  final case class FunctionTerm(label: FunctionLabel, args: Seq[Term]) extends Term {
    require(label.arity == args.size)

    override def freeVariables: Set[VariableLabel] = args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)

    override def constantFunctions: Set[ConstantFunctionLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions) + l
      case l: SchematicFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions)
    }
    override def schematicFunctions: Set[SchematicFunctionLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[SchematicFunctionLabel])((prev, next) => prev union next.schematicFunctions)
      case l: SchematicFunctionLabel => args.foldLeft(Set.empty[SchematicFunctionLabel])((prev, next) => prev union next.schematicFunctions) + l
    }

    val arity: Int = args.size
  }

}
