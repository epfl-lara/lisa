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
   * A term which consists of a single variable.
   *
   * @param label The label of the variable.
   */
  object VariableTerm extends (VariableLabel => Term){
    def apply(label: VariableLabel) : Term = Term(label, Seq())
    def unapply(t:Term): Option[VariableLabel] = t.label match {
      case l: VariableLabel => Some(l)
      case _ => None
    }
  }

  /**
   * A term labelled by a function symbol. It must contain a number of children equal to the arity of the symbol
   *
   * @param label The label of the node
   * @param args  children of the node. The number of argument must be equal to the arity of the function.
   */
  sealed case class Term(label: TermLabel, args: Seq[Term]) extends TreeWithLabel[TermLabel] {
    require(label.arity == args.size)
    override def freeVariables: Set[VariableLabel] = label match {
      case l: VariableLabel => Set(l)
      case _ => args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)
    }

    override def constantFunctions: Set[ConstantFunctionLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions) + l
      case l: SchematicTermLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions)
    }
    override def schematicTerms: Set[SchematicTermLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTerms)
      case l: SchematicTermLabel => args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTerms) + l
    }

    val arity: Int = args.size
  }

}
