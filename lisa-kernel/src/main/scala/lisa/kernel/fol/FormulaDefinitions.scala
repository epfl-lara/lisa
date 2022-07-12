package lisa.kernel.fol

/**
 * Definitions of formulas; analogous to [[TermDefinitions]].
 * Depends on [[FormulaLabelDefinitions]] and [[TermDefinitions]].
 */
private[fol] trait FormulaDefinitions extends FormulaLabelDefinitions with TermDefinitions {

  /**
   * The parent class of formulas.
   * A formula is a tree whose nodes are either terms or labeled by predicates or logical connectors.
   */
  sealed abstract class Formula extends TreeWithLabel[FormulaLabel] {

    def constantFunctions: Set[ConstantFunctionLabel]
    def schematicTerms: Set[SchematicTermLabel]

    def constantPredicates: Set[ConstantPredicateLabel]
    def schematicPredicates: Set[SchematicPredicateLabel]
  }

  /**
   * The formula counterpart of [[PredicateLabel]].
   */
  sealed case class PredicateFormula(label: PredicateLabel, args: Seq[Term]) extends Formula {
    override def freeVariables: Set[VariableLabel] = args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)

    override def constantPredicates: Set[ConstantPredicateLabel] = label match {
      case l: ConstantPredicateLabel => Set(l)
      case l: SchematicPredicateLabel => Set()
    }
    override def schematicPredicates: Set[SchematicPredicateLabel] = label match {
      case l: ConstantPredicateLabel => Set()
      case l: SchematicPredicateLabel => Set(l)
    }

    override def constantFunctions: Set[ConstantFunctionLabel] = args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions)
    override def schematicTerms: Set[SchematicTermLabel] = args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTerms)
  }

  /**
   * The formula counterpart of [[ConnectorLabel]].
   */
  sealed case class ConnectorFormula(label: ConnectorLabel, args: Seq[Formula]) extends Formula {
    override def freeVariables: Set[VariableLabel] = args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)

    override def constantFunctions: Set[ConstantFunctionLabel] = args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantFunctions)
    override def schematicTerms: Set[SchematicTermLabel] = args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTerms)

    override def constantPredicates: Set[ConstantPredicateLabel] = args.foldLeft(Set.empty[ConstantPredicateLabel])((prev, next) => prev union next.constantPredicates)
    override def schematicPredicates: Set[SchematicPredicateLabel] = args.foldLeft(Set.empty[SchematicPredicateLabel])((prev, next) => prev union next.schematicPredicates)
  }

  /**
   * The formula counterpart of [[BinderLabel]].
   */
  sealed case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula {
    override def freeVariables: Set[VariableLabel] = inner.freeVariables - bound

    override def constantFunctions: Set[ConstantFunctionLabel] = inner.constantFunctions
    override def schematicTerms: Set[SchematicTermLabel] = inner.schematicTerms -bound

    override def constantPredicates: Set[ConstantPredicateLabel] = inner.constantPredicates
    override def schematicPredicates: Set[SchematicPredicateLabel] = inner.schematicPredicates
  }

  def bindAll(binder: BinderLabel, vars: Seq[VariableLabel], phi: Formula): Formula =
    vars.foldLeft(phi)((f, v) => BinderFormula(binder, v, f))

}
