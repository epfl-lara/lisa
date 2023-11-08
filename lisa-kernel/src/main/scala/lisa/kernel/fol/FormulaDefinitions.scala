package lisa.kernel.fol

/**
 * Definitions of formulas; analogous to [[TermDefinitions]].
 * Depends on [[FormulaLabelDefinitions]] and [[TermDefinitions]].
 */
private[fol] trait FormulaDefinitions extends FormulaLabelDefinitions with TermDefinitions {

  type SimpleFormula
  def reducedForm(formula: Formula): Formula
  def reduceSet(s: Set[Formula]): Set[Formula]
  def isSameTerm(term1: Term, term2: Term): Boolean
  def isSame(formula1: Formula, formula2: Formula): Boolean
  def isImplying(formula1: Formula, formula2: Formula): Boolean
  def isSameSet(s1: Set[Formula], s2: Set[Formula]): Boolean
  def isSubset(s1: Set[Formula], s2: Set[Formula]): Boolean
  def contains(s: Set[Formula], f: Formula): Boolean

  /**
   * The parent class of formulas.
   * A formula is a tree whose nodes are either terms or labeled by predicates or logical connectors.
   */
  sealed trait Formula extends TreeWithLabel[FormulaLabel] {
    val uniqueNumber: Long = Formula.getNewId
    private[fol] var polarFormula: Option[SimpleFormula] = None
    val arity: Int = label.arity

    override def constantTermLabels: Set[ConstantFunctionLabel]
    override def schematicTermLabels: Set[SchematicTermLabel]
    override def freeSchematicTermLabels: Set[SchematicTermLabel]
    override def freeVariables: Set[VariableLabel]

    /**
     * @return The list of constant predicate symbols in the formula.
     */
    def constantPredicateLabels: Set[ConstantPredicateLabel]

    /**
     * @return The list of schematic predicate symbols in the formula, including variable formulas .
     */
    def schematicPredicateLabels: Set[SchematicVarOrPredLabel]

    /**
     * @return The list of schematic connector symbols in the formula.
     */
    def schematicConnectorLabels: Set[SchematicConnectorLabel]

    /**
     * @return The list of schematic connector, predicate and formula variable symbols in the formula.
     */
    def schematicFormulaLabels: Set[SchematicFormulaLabel] =
      (schematicPredicateLabels.toSet: Set[SchematicFormulaLabel]) union (schematicConnectorLabels.toSet: Set[SchematicFormulaLabel])

    /**
     * @return The list of free formula variable symbols in the formula
     */
    def freeVariableFormulaLabels: Set[VariableFormulaLabel]

  }
  private object Formula {
    var totalNumberOfFormulas: Long = 0
    def getNewId: Long = {
      totalNumberOfFormulas += 1
      totalNumberOfFormulas
    }
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

    override def freeVariableFormulaLabels: Set[VariableFormulaLabel] = label match {
      case l: VariableFormulaLabel => Set(l)
      case _ => Set()
    }
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
    override def freeVariableFormulaLabels: Set[VariableFormulaLabel] =
      args.foldLeft(Set.empty[VariableFormulaLabel])((prev, next) => prev union next.freeVariableFormulaLabels)
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
    override def freeVariableFormulaLabels: Set[VariableFormulaLabel] = inner.freeVariableFormulaLabels
  }
}
