package lisa.kernel.fol

/**
 * Definitions of terms; depends on [[TermLabelDefinitions]].
 */
private[fol] trait TermDefinitions extends TermLabelDefinitions {

  protected trait TreeWithLabel[A] {
    val label: A
    val arity: Int

    /**
     * @return The list of free variables in the term.
     */
    def freeVariables: Set[VariableLabel]

    /**
     * @return The list of constant (i.e. non schematic) function symbols, including of arity 0.
     */
    def constantTermLabels: Set[ConstantFunctionLabel]

    /**
     * @return The list of schematic term symbols (including free and bound variables) in the term
     */
    def schematicTermLabels: Set[SchematicTermLabel]

    /**
     * @return The list of schematic term symbols (including free variables and excluding bound variables) in the term
     */
    def freeSchematicTermLabels: Set[SchematicTermLabel]
  }

  /**
   * A term labelled by a function symbol. It must contain a number of children equal to the arity of the symbol
   *
   * @param label The label of the node
   * @param args  children of the node. The number of argument must be equal to the arity of the function.
   */
  sealed case class Term(label: TermLabel, args: Seq[Term]) extends TreeWithLabel[TermLabel] {
    require(label.arity == args.size)
    val arity: Int = label.arity

    override def freeVariables: Set[VariableLabel] = label match {
      case l: VariableLabel => Set(l)
      case _ => args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)
    }

    override def constantTermLabels: Set[ConstantFunctionLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantTermLabels) + l
      case l: SchematicTermLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantTermLabels)
    }
    override def schematicTermLabels: Set[SchematicTermLabel] = label match {
      case l: ConstantFunctionLabel => args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTermLabels)
      case l: SchematicTermLabel => args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTermLabels) + l
    }
    override def freeSchematicTermLabels: Set[SchematicTermLabel] = schematicTermLabels
  }

  /**
   * A VariableTerm is exactly an arity-0 schematic term, but we provide specific constructors and destructors.
   */
  object VariableTerm extends (VariableLabel => Term){
    /**
     * A term which consists of a single variable.
     *
     * @param label The label of the variable.
     */
    def apply(label: VariableLabel) : Term = Term(label, Seq())
    def unapply(t:Term): Option[VariableLabel] = t.label match {
      case l: VariableLabel => Some(l)
      case _ => None
    }
  }

}
