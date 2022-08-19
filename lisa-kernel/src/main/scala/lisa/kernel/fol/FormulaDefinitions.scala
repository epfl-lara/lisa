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
  sealed trait Formula extends TreeWithLabel[FormulaLabel] {
    val arity: Int = label.arity
    def constantTermLabels: Set[ConstantFunctionLabel]
    def schematicTermsLabels: Set[SchematicTermLabel]
    def freeSchematicTermsLabels: Set[SchematicTermLabel]
    def freeVariables: Set[VariableLabel]
    def constantPredicates: Set[ConstantPredicateLabel]
    def schematicPredicates: Set[SchematicPredicateLabel]
    def schematicConnectors: Set[SchematicConnectorLabel]
    def schematicFormulaLabels: Set[SchematicFormulaLabel] =
      (schematicPredicates.toSet:Set[SchematicFormulaLabel]) union (schematicConnectors.toSet:Set[SchematicFormulaLabel])

  }

  /**
   * The formula counterpart of [[PredicateLabel]].
   */
  sealed case class PredicateFormula(label: PredicateLabel, args: Seq[Term]) extends Formula {
    require(label.arity == args.size)
    override def constantTermLabels: Set[ConstantFunctionLabel] =
      args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantTermLabels)
    override def schematicTermsLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTermsLabels)
    override def freeSchematicTermsLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.freeSchematicTermsLabels)
    override def freeVariables: Set[VariableLabel] =
      args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)
    override def constantPredicates: Set[ConstantPredicateLabel] = label match {
      case l: ConstantPredicateLabel => Set(l)
      case l: SchematicPredicateLabel => Set()
    }
    override def schematicPredicates: Set[SchematicPredicateLabel] = label match {
      case l: ConstantPredicateLabel => Set()
      case l: SchematicPredicateLabel => Set(l)
    }
    override def schematicConnectors: Set[SchematicConnectorLabel] = Set()
  }

  /**
   * The formula counterpart of [[ConnectorLabel]].
   */
  sealed case class ConnectorFormula(label: ConnectorLabel, args: Seq[Formula]) extends Formula {
    require(label.arity == args.size && label.arity != 0)
    override def constantTermLabels: Set[ConstantFunctionLabel] =
      args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantTermLabels)
    override def schematicTermsLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTermsLabels)
    override def freeSchematicTermsLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.freeSchematicTermsLabels)
    override def freeVariables: Set[VariableLabel] =
      args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)
    override def constantPredicates: Set[ConstantPredicateLabel] =
      args.foldLeft(Set.empty[ConstantPredicateLabel])((prev, next) => prev union next.constantPredicates)
    override def schematicPredicates: Set[SchematicPredicateLabel] =
      args.foldLeft(Set.empty[SchematicPredicateLabel])((prev, next) => prev union next.schematicPredicates)
    override def schematicConnectors: Set[SchematicConnectorLabel] = label match {
      case l: ConstantConnectorLabel =>
        args.foldLeft(Set.empty[SchematicConnectorLabel])((prev, next) => prev union next.schematicConnectors)
      case l: SchematicConnectorLabel =>
        args.foldLeft(Set(l))((prev, next) => prev union next.schematicConnectors)
    }
  }

  /**
   * The formula counterpart of [[BinderLabel]].
   */
  sealed case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula {
    override def constantTermLabels: Set[ConstantFunctionLabel] = inner.constantTermLabels
    override def schematicTermsLabels: Set[SchematicTermLabel] = inner.schematicTermsLabels
    override def freeSchematicTermsLabels: Set[SchematicTermLabel] = inner.freeSchematicTermsLabels - bound
    override def freeVariables: Set[VariableLabel] = inner.freeVariables - bound
    override def constantPredicates: Set[ConstantPredicateLabel] = inner.constantPredicates
    override def schematicPredicates: Set[SchematicPredicateLabel] = inner.schematicPredicates
    override def schematicConnectors: Set[SchematicConnectorLabel] = inner.schematicConnectors
  }

  /**
   * Binds multiple variables at the same time
   */
  @deprecated
  def bindAll(binder: BinderLabel, vars: Seq[VariableLabel], phi: Formula): Formula =
    vars.foldLeft(phi)((f, v) => BinderFormula(binder, v, f))

}
