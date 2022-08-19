package lisa.front.fol.utils

import lisa.front.fol.conversions.to.FormulaConversionsTo
import lisa.front.fol.definitions.FormulaDefinitions
import lisa.front.fol.ops.FormulaOps

trait FormulaUtils extends TermUtils with FormulaDefinitions with FormulaConversionsTo with FormulaOps {

  type RenamedPredicate[B <: PredicateLabel[?]] = RenamedLabel[PredicateLabel[?], SchematicPredicateLabel[?], B]
  type RenamedPredicateSchema = RenamedPredicate[SchematicPredicateLabel[?]]
  extension [L <: PredicateLabel[?]](renamed: RenamedPredicate[L]) {
    def toAssignment: AssignedPredicate = {
      val parameters = freshIds(Set.empty, renamed.from.arity).map(SchematicTermLabel.apply[0])
      AssignedPredicate.unsafe(renamed.from, LambdaPredicate.unsafe(parameters, PredicateFormula.unsafe(renamed.to, parameters.map(Term.unsafe(_, Seq.empty)))))
    }
  }
  type RenamedConnector[B <: ConnectorLabel[?]] = RenamedLabel[ConnectorLabel[?], SchematicConnectorLabel[?], B]
  type RenamedConnectorSchema = RenamedConnector[SchematicConnectorLabel[?]]
  extension [L <: ConnectorLabel[?]](renamed: RenamedConnector[L]) {
    def toAssignment: AssignedConnector = {
      val parameters = freshIds(Set.empty, renamed.from.arity).map(SchematicPredicateLabel.apply[0])
      AssignedConnector.unsafe(renamed.from, LambdaConnector.unsafe(parameters, ConnectorFormula.unsafe(renamed.to, parameters.map(PredicateFormula.unsafe(_, Seq.empty)))))
    }
  }

  case class LambdaPredicate[N <: Arity] private(parameters: Seq[SchematicTermLabel[0]], body: Formula) extends LambdaDefinition[N, SchematicTermLabel[0], Formula] {
    override type U = Term
    override protected def instantiate(args: Seq[Term]): Formula =
      instantiateFormulaSchemas(body, functions = parameters.zip(args).map { case (from, to) => AssignedFunction(from, LambdaFunction(_ => to)) })
  }
  object LambdaPredicate {
    def apply[N <: Arity](f: FillArgs[SchematicTermLabel[0], N] => Formula)(using v: ValueOf[N]): LambdaPredicate[N] = {
      val n = v.value
      val dummyVariable = SchematicTermLabel[0]("")
      val taken = freeSchematicTermLabelsOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
      val (params, body) = fillTupleParameters(SchematicTermLabel.apply[0](_), n, f, taken)
      new LambdaPredicate(params.toSeq, body)
    }
    def apply(f: Formula): LambdaPredicate[0] = LambdaPredicate(Seq.empty, f)
    def unsafe(parameters: Seq[SchematicTermLabel[0]], body: Formula): LambdaPredicate[?] = new LambdaPredicate(parameters, body)
  }

  case class AssignedPredicate private(schema: SchematicPredicateLabel[?], lambda: LambdaPredicate[?])
    extends AssignedSchema[SchematicPredicateLabel[?], SchematicTermLabel[0]] {
    override type L = LambdaPredicate[?]
  }
  object AssignedPredicate {
    def apply[N <: Arity](schema: SchematicPredicateLabel[N], lambda: LambdaPredicate[N])(using v: ValueOf[N]): AssignedPredicate = new AssignedPredicate(schema, lambda)
    def unsafe(schema: SchematicPredicateLabel[?], lambda: LambdaPredicate[?]): AssignedPredicate = new AssignedPredicate(schema, lambda)
  }
  given Conversion[Formula, LambdaPredicate[0]] = LambdaPredicate.apply
  given labelToLambdaPredicate[T](using Conversion[T, Formula]): Conversion[T, LambdaPredicate[0]] = (t: T) => {
    val formula: Formula = t
    formula
  }
  //given lambdaToLambdaPredicate[N <: Arity](using ValueOf[N]): Conversion[FillArgs[SchematicTermLabel[0], N] => Formula, LambdaPredicate[N]] = LambdaPredicate.apply
  given lambdaToLambdaPredicate1: Conversion[SchematicTermLabel[0] => Formula, LambdaPredicate[1]] = LambdaPredicate.apply
  given lambdaToLambdaPredicate2: Conversion[((SchematicTermLabel[0], SchematicTermLabel[0])) => Formula, LambdaPredicate[2]] = LambdaPredicate.apply

  case class LambdaConnector[N <: Arity] private(parameters: Seq[SchematicPredicateLabel[0]], body: Formula) extends LambdaDefinition[N, SchematicPredicateLabel[0], Formula] {
    override type U = Formula
    override protected def instantiate(args: Seq[Formula]): Formula =
      instantiateFormulaSchemas(body, predicates = parameters.zip(args).map { case (from, to) => AssignedPredicate(from, LambdaPredicate(_ => to)) })
  }
  object LambdaConnector {
    def apply[N <: Arity](f: FillArgs[SchematicPredicateLabel[0], N] => Formula)(using v: ValueOf[N]): LambdaConnector[N] = {
      val n = v.value
      val dummyVariable = SchematicPredicateLabel[0]("")
      val taken = schematicPredicatesOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
      val (params, body) = fillTupleParameters(SchematicPredicateLabel.apply[0](_), n, f, taken)
      new LambdaConnector(params.toSeq, body)
    }
    def apply(f: Formula): LambdaConnector[0] = LambdaConnector(Seq.empty, f)
    def unsafe(parameters: Seq[SchematicPredicateLabel[0]], body: Formula): LambdaConnector[?] = new LambdaConnector(parameters, body)
  }
  given Conversion[Formula, LambdaConnector[0]] = LambdaConnector.apply
  given labelToLambdaConnector[T](using Conversion[T, Formula]): Conversion[T, LambdaConnector[0]] = LambdaConnector.apply
  given lambdaToLambdaConnector1: Conversion[SchematicPredicateLabel[0] => Formula, LambdaConnector[1]] = LambdaConnector.apply
  given lambdaToLambdaConnector2: Conversion[((SchematicPredicateLabel[0], SchematicPredicateLabel[0])) => Formula, LambdaConnector[2]] = LambdaConnector.apply

  case class AssignedConnector private(schema: SchematicConnectorLabel[?], lambda: LambdaConnector[?])
    extends AssignedSchema[SchematicConnectorLabel[?], SchematicPredicateLabel[0]] {
    override type L = LambdaConnector[?]
  }
  object AssignedConnector {
    def apply[N <: Arity](schema: SchematicConnectorLabel[N], lambda: LambdaConnector[N])(using v: ValueOf[N]): AssignedConnector = new AssignedConnector(schema, lambda)
    def unsafe(schema: SchematicConnectorLabel[?], lambda: LambdaConnector[?]): AssignedConnector = new AssignedConnector(schema, lambda)
  }

  object Assigned {
    def apply[N <: Arity](schema: SchematicTermLabel[N], lambda: LambdaFunction[N])(using v: ValueOf[N]): AssignedFunction = AssignedFunction(schema, lambda)
    def apply[N <: Arity](schema: SchematicPredicateLabel[N], lambda: LambdaPredicate[N])(using v: ValueOf[N]): AssignedPredicate = AssignedPredicate(schema, lambda)
    def apply[N <: Arity](schema: SchematicConnectorLabel[N], lambda: LambdaConnector[N])(using v: ValueOf[N]): AssignedConnector = AssignedConnector(schema, lambda)
  }

  def toKernel(lambda: LambdaPredicate[?]): lisa.kernel.fol.FOL.LambdaTermFormula =
    lisa.kernel.fol.FOL.LambdaTermFormula(lambda.parameters.map((label: SchematicTermLabel[0]) => {
      val r = toKernel(label)
      r
    }), lambda.body)
  given Conversion[LambdaPredicate[?], lisa.kernel.fol.FOL.LambdaTermFormula] = toKernel

  def toKernel(lambda: LambdaConnector[?]): lisa.kernel.fol.FOL.LambdaFormulaFormula =
    lisa.kernel.fol.FOL.LambdaFormulaFormula(lambda.parameters.map(toKernel), lambda.body)
  given Conversion[LambdaConnector[?], lisa.kernel.fol.FOL.LambdaFormulaFormula] = toKernel

  /**
   * A simple procedure to handle the fact that the kernel does not support schematic connectors.
   * These will be converted into fresh constant connectors, which can be considered equivalent when used in some context (e.g. equivalence checking).
   * @param formulas the formulas to be adapted
   * @return new formulas that have been adapted
   */
  def adaptConnectorSchemas(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] = {
    def recursive(formula: Formula, predicates: Set[SchematicPredicateLabel[?]], translation: Map[ConnectorFormula, SchematicPredicateLabel[?]]):
    (Formula, Set[SchematicPredicateLabel[?]], Map[ConnectorFormula, SchematicPredicateLabel[?]]) = formula match {
      case other: PredicateFormula => (other, predicates, translation)
      case connector @ ConnectorFormula(label, args) =>
        label match {
          case schematic: SchematicConnectorLabel[?] =>
            translation.get(connector) match {
              case Some(predicate) => (PredicateFormula.unsafe(predicate, Seq.empty), predicates, translation)
              case None =>
                val newId = freshId(predicates.map(_.id), schematic.id)
                val newLabel = SchematicPredicateLabel[0](newId)
                (PredicateFormula.unsafe(newLabel, Seq.empty), predicates + newLabel, translation + (connector -> newLabel))
            }
          case _ =>
            val (newFormulas, newAllPredicates, newAllTranslation) = args.foldLeft((Seq.empty[Formula], predicates, translation)) {
              case ((acc, accPredicates, accTranslation), arg) =>
                val (newFormula, np, nt) = recursive(arg, accPredicates, accTranslation)
                (acc :+ newFormula, np, nt)
            }
            (ConnectorFormula.unsafe(label, newFormulas), newAllPredicates, newAllTranslation)
        }
      case BinderFormula(label, bound, inner) =>
        val (newInner, newPredicates, newTranslation) = recursive(inner, predicates, translation)
        (BinderFormula(label, bound, newInner), newPredicates, newTranslation)
    }
    val schematicPredicates = formulas.flatMap(schematicPredicatesOf).toSet
    val (translatedFormulas, _, _) = formulas.foldLeft((IndexedSeq.empty[Formula], schematicPredicates, Map.empty[ConnectorFormula, SchematicPredicateLabel[?]])) {
      case ((acc, taken, currentTranslation), formula) =>
        val (translatedFormula, newTaken, newTranslation) = recursive(formula, taken, currentTranslation)
        (acc :+ translatedFormula, newTaken, newTranslation)
    }
    translatedFormulas
  }

  /** @see [[lisa.kernel.fol.FOL.isSame]] */
  def isSame(f1: Formula, f2: Formula): Boolean =
    adaptConnectorSchemas(IndexedSeq(f1, f2)) match {
      case IndexedSeq(af1, af2) =>
        lisa.kernel.fol.FOL.isSame(af1, af2)
      case e => throw new MatchError(e)
    }

  /** @see [[lisa.kernel.fol.FOL.Formula#freeVariables]] */
  def freeVariablesOf(formula: Formula): Set[VariableLabel] = formula match {
    case PredicateFormula(_, args) => args.flatMap(freeVariablesOf).toSet
    case ConnectorFormula(_, args) => args.flatMap(freeVariablesOf).toSet
    case BinderFormula(_, bound, inner) => freeVariablesOf(inner) - bound
  }

  def freeTermLabelsOf(formula: Formula): Set[TermLabel[?]] = formula match {
    case PredicateFormula(_, args) => args.flatMap(termLabelsOf).toSet
    case ConnectorFormula(_, args) => args.flatMap(termLabelsOf).toSet
    case BinderFormula(_, bound, inner) => termLabelsOf(inner) - bound
  }
  def termLabelsOf(formula: Formula): Set[TermLabel[?]] = formula match {
    case PredicateFormula(_, args) => args.flatMap(termLabelsOf).toSet
    case ConnectorFormula(_, args) => args.flatMap(termLabelsOf).toSet
    case BinderFormula(_, bound, inner) => termLabelsOf(inner)
  }

  /** @see [[lisa.kernel.fol.FOL.Formula#schematicFunctions]] */
  def freeSchematicTermLabelsOf(formula: Formula): Set[SchematicTermLabel[?]] =
    freeTermLabelsOf(formula).collect { case schematic: SchematicTermLabel[?] => schematic }

  def schematicTermLabelsOf(formula: Formula): Set[SchematicTermLabel[?]] =
    termLabelsOf(formula).collect { case schematic: SchematicTermLabel[?] => schematic }

  def predicatesOf(formula: Formula): Set[PredicateLabel[?]] = formula match {
    case PredicateFormula(label, _) => Set(label)
    case ConnectorFormula(_, args) => args.flatMap(predicatesOf).toSet
    case BinderFormula(_, _, inner) => predicatesOf(inner)
  }

  /** @see [[lisa.kernel.fol.FOL.Formula#schematicPredicates]] */
  def schematicPredicatesOf(formula: Formula): Set[SchematicPredicateLabel[?]] =
    predicatesOf(formula).collect { case schematic: SchematicPredicateLabel[?] => schematic }

  def schematicConnectorsOf(formula: Formula): Set[SchematicConnectorLabel[?]] = formula match {
    case PredicateFormula(_, _) => Set.empty
    case ConnectorFormula(label, args) =>
      val set = label match {
        case _: ConstantConnectorLabel[?] => Set.empty
        case schematic: SchematicConnectorLabel[?] => Set(schematic)
      }
      set ++ args.flatMap(schematicConnectorsOf)
    case BinderFormula(_, _, inner) => schematicConnectorsOf(inner)
  }

  def declaredBoundVariablesOf(formula: Formula): Set[VariableLabel] = formula match {
    case PredicateFormula(_, _) => Set.empty
    case ConnectorFormula(_, args) => args.flatMap(declaredBoundVariablesOf).toSet
    case BinderFormula(_, bound, inner) => declaredBoundVariablesOf(inner) + bound
  }


  protected def isFormulaWellFormed(formula: Formula)(using ctx: Scope): Boolean = formula match {
    case PredicateFormula(label, args) => args.forall(isWellFormed)
    case ConnectorFormula(_: SchematicConnectorLabel[?], Seq()) => false // Use nullary predicates instead
    case ConnectorFormula(label, args) => args.forall(isFormulaWellFormed)
    case BinderFormula(_, bound, inner) =>
      !ctx.boundVariables.contains(bound) && isFormulaWellFormed(inner)(using ctx.copy(boundVariables = ctx.boundVariables + bound))
  }

  def isWellFormed(formula: Formula): Boolean = isFormulaWellFormed(formula)(using Scope())


  def substituteVariables(formula: Formula, map: Map[VariableLabel, Term]): Formula = formula match {
    case PredicateFormula(label, args) => PredicateFormula.unsafe(label, args.map(substituteVariables(_, map)))
    case ConnectorFormula(label, args) => ConnectorFormula.unsafe(label, args.map(substituteVariables(_, map)))
    case BinderFormula(label, bound, inner) =>
      val newSubst = map - bound
      val fv = map.values.flatMap(freeVariablesOf).toSet
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.id), bound.id))
        val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
        BinderFormula(label, newBoundVariable, substituteVariables(newInner, newSubst))
      } else {
        BinderFormula(label, bound, substituteVariables(inner, newSubst))
      }
  }

  def instantiateFormulaSchemas(
    formula: Formula,
    functions: Seq[AssignedFunction] = Seq.empty,
    predicates: Seq[AssignedPredicate] = Seq.empty,
    connectors: Seq[AssignedConnector] = Seq.empty,
  ): Formula = {
    val predicatesMap: Map[SchematicPredicateLabel[?], LambdaPredicate[?]] = predicates.map(i => i.schema -> i.lambda).toMap
    val connectorsMap: Map[SchematicConnectorLabel[?], LambdaConnector[?]] = connectors.map(i => i.schema -> i.lambda).toMap
    def instantiateInternal(formula: Formula): Formula = formula match {
      case PredicateFormula(label, args) =>
        lazy val newArgs = args.map(instantiateTermSchemas(_, functions))
        label match {
          case f: SchematicPredicateLabel[?] if predicatesMap.contains(f) => predicatesMap(f).unsafe(newArgs)
          case _ => PredicateFormula.unsafe(label, newArgs)
        }
      case ConnectorFormula(label, args) =>
        lazy val newArgs = args.map(instantiateInternal)
        label match {
          case f: SchematicConnectorLabel[?] if connectorsMap.contains(f) => connectorsMap(f).unsafe(newArgs)
          case _ => ConnectorFormula.unsafe(label, newArgs)
        }
      case BinderFormula(label, bound, inner) =>
        //TODO Requires testing. Match against substituteVariables
        val newFuns = functions.filterNot(i => i.schema == bound)
        val fv = newFuns.flatMap(f => freeVariablesOf(f.lambda.body)).toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.id), bound.id))
          val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiateFormulaSchemas(newInner, newFuns, predicates, connectors))
        } else {
          BinderFormula(label, bound, instantiateFormulaSchemas(inner, newFuns, predicates, connectors))
        }
    }
    instantiateInternal(formula)
  }

  def unsafeRenameVariables(formula: Formula, map: Map[VariableLabel, VariableLabel]): Formula = formula match {
    case PredicateFormula(label, args) =>
      PredicateFormula.unsafe(label, args.map(unsafeRenameVariables(_, map)))
    case ConnectorFormula(label, args) =>
      ConnectorFormula.unsafe(label, args.map(unsafeRenameVariables(_, map)))
    case BinderFormula(label, bound, inner) =>
      val newBound = map.getOrElse(bound, bound)
      BinderFormula(label, newBound, unsafeRenameVariables(inner, map))
  }

}
