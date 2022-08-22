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
    def schematicTermLabels: Set[SchematicTermLabel]
    def freeSchematicTermLabels: Set[SchematicTermLabel]
    def freeVariables: Set[VariableLabel]
    def constantPredicateLabels: Set[ConstantPredicateLabel]
    def schematicPredicateLabels: Set[SchematicVarOrPredLabel]
    def schematicConnectorLabels: Set[SchematicConnectorLabel]
    def schematicFormulaLabels: Set[SchematicFormulaLabel] =
      (schematicPredicateLabels.toSet:Set[SchematicFormulaLabel]) union (schematicConnectorLabels.toSet:Set[SchematicFormulaLabel])

  }

  /**
   * The formula counterpart of [[PredicateLabel]].
   */
  sealed case class PredicateFormula(label: PredicateLabel, args: Seq[Term]) extends Formula {
    require(label.arity == args.size)
    override def constantTermLabels: Set[ConstantFunctionLabel] =
      args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantTermLabels)
    override def schematicTermLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTermLabels)
    override def freeSchematicTermLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.freeSchematicTermLabels)
    override def freeVariables: Set[VariableLabel] =
      args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)
    override def constantPredicateLabels: Set[ConstantPredicateLabel] = label match {
      case l: ConstantPredicateLabel => Set(l)
      case _ => Set()
    }
    override def schematicPredicateLabels: Set[SchematicVarOrPredLabel] = label match {
      case l: SchematicVarOrPredLabel => Set(l)
      case _ => Set()
    }
    override def schematicConnectorLabels: Set[SchematicConnectorLabel] = Set()
  }

  /**
   * The formula counterpart of [[ConnectorLabel]].
   */
  sealed case class ConnectorFormula(label: ConnectorLabel, args: Seq[Formula]) extends Formula {
    require(label.arity == args.size || label.arity == -1)
    require(label.arity != 0)
    override def constantTermLabels: Set[ConstantFunctionLabel] =
      args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.constantTermLabels)
    override def schematicTermLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.schematicTermLabels)
    override def freeSchematicTermLabels: Set[SchematicTermLabel] =
      args.foldLeft(Set.empty[SchematicTermLabel])((prev, next) => prev union next.freeSchematicTermLabels)
    override def freeVariables: Set[VariableLabel] =
      args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)
    override def constantPredicateLabels: Set[ConstantPredicateLabel] =
      args.foldLeft(Set.empty[ConstantPredicateLabel])((prev, next) => prev union next.constantPredicateLabels)
    override def schematicPredicateLabels: Set[SchematicVarOrPredLabel] =
      args.foldLeft(Set.empty[SchematicVarOrPredLabel])((prev, next) => prev union next.schematicPredicateLabels)
    override def schematicConnectorLabels: Set[SchematicConnectorLabel] = label match {
      case l: ConstantConnectorLabel =>
        args.foldLeft(Set.empty[SchematicConnectorLabel])((prev, next) => prev union next.schematicConnectorLabels)
      case l: SchematicConnectorLabel =>
        args.foldLeft(Set(l))((prev, next) => prev union next.schematicConnectorLabels)
    }
  }

  /**
   * The formula counterpart of [[BinderLabel]].
   */
  sealed case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula {
    override def constantTermLabels: Set[ConstantFunctionLabel] = inner.constantTermLabels
    override def schematicTermLabels: Set[SchematicTermLabel] = inner.schematicTermLabels
    override def freeSchematicTermLabels: Set[SchematicTermLabel] = inner.freeSchematicTermLabels - bound
    override def freeVariables: Set[VariableLabel] = inner.freeVariables - bound
    override def constantPredicateLabels: Set[ConstantPredicateLabel] = inner.constantPredicateLabels
    override def schematicPredicateLabels: Set[SchematicVarOrPredLabel] = inner.schematicPredicateLabels
    override def schematicConnectorLabels: Set[SchematicConnectorLabel] = inner.schematicConnectorLabels
  }

  /**
   * Binds multiple variables at the same time
   */
  @deprecated
  def bindAll(binder: BinderLabel, vars: Seq[VariableLabel], phi: Formula): Formula =
    vars.foldLeft(phi)((f, v) => BinderFormula(binder, v, f))

}
