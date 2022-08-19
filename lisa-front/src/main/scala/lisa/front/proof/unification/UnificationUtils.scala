package lisa.front.proof.unification

import lisa.front.proof.sequent.SequentDefinitions
import lisa.front.fol.FOL.*

import scala.collection.View

trait UnificationUtils extends UnificationDefinitions with SequentDefinitions {

  /**
   * Whether a collection of patterns is legal (e.g. no malformed formulas, no clashing variables, ...)
   * @param patterns the patterns to check
   * @return whether the patterns are legal or not
   */
  def isLegalPatterns(patterns: IndexedSeq[PartialSequent]): Boolean = {
    lazy val boundVariables = patterns.flatMap(declaredBoundVariablesOfSequent)

    // Applications match arity, no clashing bound variable patterns
    lazy val noMalformedFormulas = patterns.forall(isSequentWellFormed)
    // Declared variable patterns must have a globally unique name
    lazy val noClashingBoundVariablePatterns = boundVariables.distinct.size == boundVariables.size
    // Free variables should not reuse a name of a bound variable
    lazy val noConflictingBoundFreeVariables = boundVariables.intersect(patterns.flatMap(freeVariablesOfSequent)).isEmpty

    noMalformedFormulas && noClashingBoundVariablePatterns && noConflictingBoundFreeVariables
  }

  /**
   * Inflates patterns using a context.
   * @param patternsTo the patterns to inflate
   * @param valuesFrom the values on the other side
   * @param ctx the assignment
   * @param indices the indices of the formulas that have been matched in the values
   * @return the inflated values
   */
  private def inflateValues(
    patternsTo: IndexedSeq[PartialSequent],
    valuesFrom: IndexedSeq[Sequent],
    ctx: UnificationContext,
    indices: IndexedSeq[(IndexedSeq[Int], IndexedSeq[Int])]
  ): IndexedSeq[Sequent] = {
    def removeIndices[T](array: IndexedSeq[T], indices: Seq[Int]): IndexedSeq[T] = {
      val set = indices.toSet
      for {
        (v, i) <- array.zipWithIndex
          if !set.contains(i)
      } yield v
    }

    def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
      formulas.map(formula => instantiateFormulaSchemas(
        unsafeRenameVariables(formula, ctx.variables),
        functions = ctx.assignedFunctions, predicates = ctx.assignedPredicates, connectors = ctx.assignedConnectors))

    def createValueTo(common: IndexedSeq[Formula], pattern: IndexedSeq[Formula], partial: Boolean): IndexedSeq[Formula] = {
      val instantiated = instantiate(pattern)
      if(partial) common ++ instantiated else instantiated
    }

    val (commonLeft, commonRight) = {
      indices.zip(valuesFrom).map { case ((indicesLeft, indicesRight), Sequent(valueLeft, valueRight)) => // Union all
        (removeIndices(valueLeft, indicesLeft), removeIndices(valueRight, indicesRight))
      }.foldLeft((IndexedSeq.empty[Formula], IndexedSeq.empty[Formula])) { case ((accL, accR), ((ls, rs))) =>
        (accL ++ ls.diff(accL), accR ++ rs.diff(accR))
      }
    }

    val newValues = patternsTo.map(patternTo =>
      Sequent(
        createValueTo(commonLeft, patternTo.left, patternTo.partialLeft),
        createValueTo(commonRight, patternTo.right, patternTo.partialRight),
      )
    )

    newValues
  }

  private type Constraints = Seq[Constraint]
  private type ConstraintsResult = Option[Constraints]

  private type Context = Set[(VariableLabel, VariableLabel)]

  /**
   * A constraint represents an equation between a label and a pattern.
   * The constraint can be resolved as soon as the pattern can be fully instantiated to a value.
   */
  private enum Constraint {
    case SchematicFunction(label: SchematicTermLabel[?], args: Seq[Term], value: Term, ctx: Context)
    case SchematicPredicate(label: SchematicPredicateLabel[?], args: Seq[Term], value: Formula, ctx: Context)
    case SchematicConnector(label: SchematicConnectorLabel[?], args: Seq[Formula], value: Formula, ctx: Context)
    case Variable(pattern: VariableLabel, value: VariableLabel)
  }
  import Constraint.*

  private val empty: ConstraintsResult = Some(Seq.empty)
  private def merge(o1: ConstraintsResult, o2: ConstraintsResult): ConstraintsResult =
    for {
      c1 <- o1
        c2 <- o2
    } yield c1 ++ c2
  private def collectRecursiveTerm(
    pattern: Term,
    value: Term,
    valuesFunctions: Set[SchematicTermLabel[?]], valuesVariables: Set[VariableLabel],
  )(using ctx: Context): ConstraintsResult = (pattern, value) match {
    case (Term(labelPattern: TermLabel[?], argsPattern), Term(labelValue: TermLabel[?], argsValue)) if labelPattern == labelValue =>
      argsPattern.zip(argsValue).map { case (argPattern, argValue) => collectRecursiveTerm(argPattern, argValue, valuesFunctions, valuesVariables) }.fold(empty)(merge)
    case (Term(labelPattern: SchematicTermLabel[?], argsPattern), _) if !valuesFunctions.contains(labelPattern) =>
      Some(Seq(SchematicFunction(labelPattern, argsPattern, value, ctx)))
    case (VariableTerm(labelPattern), VariableTerm(labelValue)) =>
      if(valuesVariables.contains(labelPattern)) {
        if(labelPattern == labelValue) {
          Some(Seq.empty)
        } else {
          None
        }
      } else if(ctx.contains((labelPattern, labelValue))) { // Bound variable
        Some(Seq(Variable(labelPattern, labelValue)))
      } else if(ctx.forall { case (p, v) => p != labelPattern && v != labelValue }) { // Free variable
        Some(Seq(Variable(labelPattern, labelValue))) // TODO merge these branches
      } else {
        None
      }
    case _ => None
  }
  private def collectRecursiveFormula(
    pattern: Formula,
    value: Formula,
    valuesFunctions: Set[SchematicTermLabel[?]], valuesPredicates: Set[SchematicPredicateLabel[?]], valuesConnectors: Set[SchematicConnectorLabel[?]], valuesVariables: Set[VariableLabel],
  )(using ctx: Set[(VariableLabel, VariableLabel)]): ConstraintsResult = (pattern, value) match {
    case (PredicateFormula(labelPattern: PredicateLabel[?], argsPattern), PredicateFormula(labelValue: PredicateLabel[?], argsValue)) if labelPattern == labelValue =>
      argsPattern.zip(argsValue).map { case (argPattern, argValue) => collectRecursiveTerm(argPattern, argValue, valuesFunctions, valuesVariables) }.fold(empty)(merge)
    case (PredicateFormula(labelPattern: SchematicPredicateLabel[?], argsPattern), _) if !valuesPredicates.contains(labelPattern) =>
      Some(Seq(SchematicPredicate(labelPattern, argsPattern, value, ctx)))
    case (ConnectorFormula(labelPattern: ConnectorLabel[?], argsPattern), ConnectorFormula(labelValue: ConnectorLabel[?], argsValue)) if labelPattern == labelValue =>
      argsPattern.zip(argsValue).map { case (argPattern, argValue) => collectRecursiveFormula(argPattern, argValue, valuesFunctions, valuesPredicates, valuesConnectors, valuesVariables) }.fold(empty)(merge)
    case (ConnectorFormula(labelPattern: SchematicConnectorLabel[?], argsPattern), _) if !valuesConnectors.contains(labelPattern) =>
      Some(Seq(SchematicConnector(labelPattern, argsPattern, value, ctx)))
    case (BinderFormula(labelPattern, boundPattern, innerPattern), BinderFormula(labelValue, boundValue, innerValue)) if labelPattern == labelValue =>
      collectRecursiveFormula(innerPattern, innerValue, valuesFunctions, valuesPredicates, valuesConnectors, valuesVariables)(using ctx + ((boundPattern, boundValue))).map(Variable(boundPattern, boundValue) +: _)
    case _ => None
  }

  private def collect(
    patternsAndValues: IndexedSeq[(Formula, Formula)],
    valuesFunctions: Set[SchematicTermLabel[?]],
    valuesPredicates: Set[SchematicPredicateLabel[?]],
    valuesConnectors: Set[SchematicConnectorLabel[?]],
    valuesVariables: Set[VariableLabel],
  ): ConstraintsResult =
    patternsAndValues.map { case (pattern, value) => collectRecursiveFormula(pattern, value, valuesFunctions, valuesPredicates, valuesConnectors, valuesVariables)(using Set.empty) }.fold(empty)(merge)

  private def unifyFromConstraints(
    constraints: Constraints,
    partialAssignment: UnificationContext,
    valueFunctions: Set[SchematicTermLabel[?]],
    valuePredicates: Set[SchematicPredicateLabel[?]],
    valueConnectors: Set[SchematicConnectorLabel[?]],
    valueVariables: Set[VariableLabel],
  ): Option[UnificationContext] = {
    if(constraints.nonEmpty) {
      def isSolvableTerm(pattern: Term)(using ctx: Set[VariableLabel]): Boolean = pattern match {
        case VariableTerm(label) => valueVariables.contains(label) || partialAssignment.variables.contains(label)
        case Term(_: ConstantFunctionLabel[?], args) => args.forall(isSolvableTerm)
        case Term(schematic: SchematicTermLabel[?], args) => (valueFunctions.contains(schematic) || partialAssignment.functions.contains(schematic)) && args.forall(isSolvableTerm)
        case _ => false
      }
      def isSolvableFormula(pattern: Formula)(using ctx: Set[VariableLabel]): Boolean = pattern match {
        case PredicateFormula(_: ConstantPredicateLabel[?], args) => args.forall(isSolvableTerm)
        case PredicateFormula(schematic: SchematicPredicateLabel[?], args) => (valuePredicates.contains(schematic) || partialAssignment.predicates.contains(schematic)) && args.forall(isSolvableTerm)
        case ConnectorFormula(_: ConstantConnectorLabel[?], args) => args.forall(isSolvableFormula)
        case ConnectorFormula(schematic: SchematicConnectorLabel[?], args) => (valueConnectors.contains(schematic) || partialAssignment.connectors.contains(schematic)) && args.forall(isSolvableFormula)
        case BinderFormula(_, bound, inner) => valueVariables.contains(bound) && isSolvableFormula(inner)(using ctx + bound)
        case _ => false
      }

      // This function tries to factor out all occurrences of `args._2` into `args._1` within `term`, and will store the result in `assignment`
      def greedyFactoringFunction(term: Term, args: IndexedSeq[(SchematicTermLabel[0], Term)], assignment: Map[SchematicTermLabel[0], Term]): (Term, Map[SchematicTermLabel[0], Term]) = {
        args.find { case (_, t) => isSame(term, instantiateTermPartial(t)) } match {
          case Some((variable, value)) => (variable, if(!assignment.contains(variable)) assignment + (variable -> value) else assignment)
          case None =>
            term match {
              case Term(label, fArgs) =>
                val (finalArgs, finalAssignment) = fArgs.foldLeft((Seq.empty[Term], assignment)) { case ((argsAcc, currentAssignment), arg) =>
                  val (newTerm, newAssignment) = greedyFactoringFunction(arg, args, currentAssignment)
                  (argsAcc :+ newTerm, newAssignment)
                }
                (Term.unsafe(label, finalArgs), finalAssignment)
            }
        }
      }

      def greedyFactoringPredicate(formula: Formula, args: IndexedSeq[(SchematicTermLabel[0], Term)], assignment: Map[SchematicTermLabel[0], Term]): (Formula, Map[SchematicTermLabel[0], Term]) = {
        formula match {
          case PredicateFormula(label, fArgs) =>
            val (finalAssignment, finalFArgs) = fArgs.foldLeft((assignment, Seq.empty[Term])) { case ((currentAssignment, currentFArgs), a) =>
              val (newA, newAssignment) = greedyFactoringFunction(a, args, currentAssignment)
              (newAssignment, currentFArgs :+ newA)
            }
            (PredicateFormula.unsafe(label, finalFArgs), finalAssignment)
          case ConnectorFormula(label, fArgs) =>
            val (finalArgs, finalAssignment) = fArgs.foldLeft((Seq.empty[Formula], assignment)) { case ((argsAcc, currentAssignment), arg) =>
              val (newFormula, newAssignment) = greedyFactoringPredicate(arg, args, currentAssignment)
              (argsAcc :+ newFormula, newAssignment)
            }
            (ConnectorFormula.unsafe(label, finalArgs), finalAssignment)
          case BinderFormula(label, bound, inner) =>
            val (factoredInner, finalAssignment) = greedyFactoringPredicate(inner, args, assignment)
            (BinderFormula(label, bound, factoredInner), finalAssignment)
        }
      }

      def greedyFactoringConnector(formula: Formula, args: IndexedSeq[(SchematicPredicateLabel[0], Formula)], assignment: Map[SchematicPredicateLabel[0], Formula]): (Formula, Map[SchematicPredicateLabel[0], Formula]) = {
        args.find { case (_, f) => isSame(formula, instantiateFormulaPartial(f)) } match {
          case Some((variable, value)) => (variable, if(!assignment.contains(variable)) assignment + (variable -> value) else assignment)
          case None =>
            formula match {
              case _: PredicateFormula => (formula, assignment) // Identity
              case ConnectorFormula(label, fArgs) =>
                val (finalArgs, finalAssignment) = fArgs.foldLeft((Seq.empty[Formula], assignment)) { case ((argsAcc, currentAssignment), arg) =>
                  val (newFormula, newAssignment) = greedyFactoringConnector(arg, args, currentAssignment)
                  (argsAcc :+ newFormula, newAssignment)
                }
                (ConnectorFormula.unsafe(label, finalArgs), finalAssignment)
              case BinderFormula(label, bound, inner) =>
                val (factoredInner, finalAssignment) = greedyFactoringConnector(inner, args, assignment)
                (BinderFormula(label, bound, factoredInner), finalAssignment)
            }
        }
      }

      def instantiateTermPartial(term: Term): Term =
        instantiateTermSchemas(term, partialAssignment.assignedFunctions)
      def instantiateFormulaPartial(formula: Formula): Formula =
        instantiateFormulaSchemas(formula, partialAssignment.assignedFunctions, partialAssignment.assignedPredicates, partialAssignment.assignedConnectors)

      def isFormulaBodyNoBoundVariables(body: Formula, ctx: Context): Boolean =
        ctx.map(_._2).intersect(freeVariablesOf(body)).isEmpty
      def isTermBodyNoBoundVariables(body: Term, ctx: Context): Boolean =
        ctx.map(_._2).intersect(freeVariablesOf(body)).isEmpty

      // The method tries to resolve a constraint and returns two nested options:
      // * None => the constraint is unsolvable (e.g. too many degrees of freedom)
      // * Some(None) => there is a contradiction
      def handler(constraint: Constraint): Option[Option[(Constraints, UnificationContext)]] = constraint match {
        case SchematicFunction(label, args, value, ctx) if partialAssignment.functions.contains(label) =>
          val lambda = partialAssignment.functions(label)
          if(!isTermBodyNoBoundVariables(lambda.body, ctx)) {
            // All the bound variables must appear in a way or another as arguments of this lambda
            Some(None)
          } else if(isSame(value, lambda.unsafe(args.map(instantiateTermPartial)))) {
            Some(Some((IndexedSeq.empty, partialAssignment)))
          } else {
            collectRecursiveTerm(lambda.unsafe(args), value, valueFunctions, valueVariables)(using ctx) match {
              case Some(addedConstraints) => Some(Some(addedConstraints, partialAssignment))
              case None => Some(None)
            }
          }
        case SchematicFunction(label, args, value, ctx) if args.forall(isSolvableTerm(_)(using ctx.map(_._1))) =>
          // TODO are all bound variables already instantiated?
          val valueArgs = args.map(unsafeRenameVariables(_, ctx.toMap))
          val freshArguments = freshIds(schematicTermLabelsOf(value).map(_.id), valueArgs.size).map(SchematicTermLabel.apply[0])
          // We drop the resulting arguments map (because it is not needed anymore)
          val (fBody, _) = greedyFactoringFunction(value, freshArguments.zip(valueArgs).toIndexedSeq, Map.empty)
          if(isTermBodyNoBoundVariables(fBody, ctx)) {
            Some(Some((IndexedSeq.empty, partialAssignment + AssignedFunction.unsafe(label, LambdaFunction.unsafe(freshArguments, fBody)))))
          } else {
            Some(None)
          }
        case SchematicPredicate(label, args, value, ctx) if partialAssignment.predicates.contains(label) =>
          val lambda = partialAssignment.predicates(label)
          if(!isFormulaBodyNoBoundVariables(lambda.body, ctx)) {
            Some(None)
          } else if(isSame(value, lambda.unsafe(args.map(instantiateTermPartial)))) {
            Some(Some((IndexedSeq.empty, partialAssignment)))
          } else {
            collectRecursiveFormula(lambda.unsafe(args), value, valueFunctions, valuePredicates, valueConnectors, valueVariables)(using ctx) match {
              case Some(addedConstraints) => Some(Some(addedConstraints, partialAssignment))
              case None => Some(None)
            }
          }
        case SchematicPredicate(label, args, value, ctx) if args.forall(isSolvableTerm(_)(using ctx.map(_._1))) =>
          // Analogous to the above
          val valueArgs = args.map(unsafeRenameVariables(_, ctx.toMap))
          val freshArguments = freshIds(schematicTermLabelsOf(value).map(_.id), valueArgs.size).map(SchematicTermLabel.apply[0])
          val (fBody, _) = greedyFactoringPredicate(value, freshArguments.zip(valueArgs).toIndexedSeq, Map.empty)
          if(isFormulaBodyNoBoundVariables(fBody, ctx)) {
            Some(Some((IndexedSeq.empty, partialAssignment + AssignedPredicate.unsafe(label, LambdaPredicate.unsafe(freshArguments, fBody)))))
          } else {
            Some(None)
          }
        case SchematicConnector(label, args, value, ctx) if partialAssignment.connectors.contains(label) =>
          val lambda = partialAssignment.connectors(label)
          if(!isFormulaBodyNoBoundVariables(lambda.body, ctx)) {
            Some(None)
          } else if(isSame(value, lambda.unsafe(args.map(instantiateFormulaPartial)))) {
            Some(Some((IndexedSeq.empty, partialAssignment)))
          } else {
            collectRecursiveFormula(lambda.unsafe(args), value, valueFunctions, valuePredicates, valueConnectors, valueVariables)(using ctx) match {
              case Some(addedConstraints) => Some(Some(addedConstraints, partialAssignment))
              case None => Some(None)
            }
          }
        case SchematicConnector(label, args, value, ctx) if args.forall(isSolvableFormula(_)(using ctx.map(_._1))) =>
          val valueArgs = args.map(unsafeRenameVariables(_, ctx.toMap))
          val freshArguments = freshIds(schematicPredicatesOf(value).map(_.id), valueArgs.size).map(SchematicPredicateLabel.apply[0])
          val (fBody, _) = greedyFactoringConnector(value, freshArguments.zip(valueArgs).toIndexedSeq, Map.empty)
          if(isFormulaBodyNoBoundVariables(fBody, ctx)) {
            Some(Some((IndexedSeq.empty, partialAssignment + AssignedConnector.unsafe(label, LambdaConnector.unsafe(freshArguments, fBody)))))
          } else {
            Some(None)
          }
        case Variable(pattern, value) =>
          if(valueVariables.contains(pattern)) {
            if(pattern == value) {
              Some(Some((IndexedSeq.empty, partialAssignment)))
            } else {
              Some(None)
            }
          } else if(partialAssignment.variables.forall { case (l, r) => l != pattern || r == value }) {
            Some(Some((IndexedSeq.empty, partialAssignment + (pattern -> value))))
          } else {
            Some(None) // Contradiction
          }
        case _ => None
      }
      constraints.view.zipWithIndex.flatMap { case (constraint, i) =>
        handler(constraint).map(_.map { case (newConstraints, newContext) => (newConstraints, newContext, i) })
      }.headOption match {
        case Some(option) => option match {
          case Some((newConstraints, newContext, i)) =>
            unifyFromConstraints(constraints.take(i) ++ newConstraints ++ constraints.drop(i + 1), newContext,
              valueFunctions, valuePredicates, valueConnectors, valueVariables)
          case None => None // Explicit error
        }
        case None => None // No available reduction
      }
    } else {
      Some(partialAssignment)
    }
  }

  /**
   * Solves a matching (one-sided unification) problem.
   * The result if any is an assignment for the patterns such that they become equivalent to the values.
   * An optional partial assignment can be provided to help or constraint the matching.
   * Additionally, it is possible to provide other patterns. In that case, the resulting sequents
   * will also include all the unmatched formulas.
   * @param patterns the patterns
   * @param values the value
   * @param otherPatterns other patterns
   * @param partialAssignment the partial assignment (or empty if none)
   * @param formulaIndices the correspondence between patterns and values in the sequents
   * @return an option containing the inflated other patterns and the assignment
   */
  def unifyAndResolve(
    patterns: IndexedSeq[PartialSequent],
    values: IndexedSeq[Sequent],
    otherPatterns: IndexedSeq[PartialSequent],
    partialAssignment: UnificationContext,
    formulaIndices: IndexedSeq[(IndexedSeq[Int], IndexedSeq[Int])]
  ): Option[(IndexedSeq[Sequent], UnificationContext)] = {

    def schemasOf(sequents: IndexedSeq[SequentBase]):
    (Set[SchematicTermLabel[?]], Set[SchematicPredicateLabel[?]], Set[SchematicConnectorLabel[?]], Set[VariableLabel], Set[VariableLabel]) =
      (sequents.flatMap(schematicFunctionsOfSequent).toSet,
        sequents.flatMap(schematicPredicatesOfSequent).toSet,
        sequents.flatMap(schematicConnectorsOfSequent).toSet,
        sequents.flatMap(freeVariablesOfSequent).toSet,
        sequents.flatMap(declaredBoundVariablesOfSequent).toSet)

    val (patternsFunctions, patternsPredicates, patternsConnectors, patternsFreeVariables, patternsBoundVariables) =
      schemasOf(patterns)
    val (valuesFunctions, valuesPredicates, valuesConnectors, valuesFreeVariables, valuesBoundVariables) =
      schemasOf(values)
    val (otherPatternsFunctions, otherPatternsPredicates, otherPatternsConnectors, otherPatternsFreeVariables, otherPatternsBoundVariables) =
      schemasOf(otherPatterns)
    val (partialAssignedFunctions, partialAssignedPredicates, partialAssignedConnectors) =
      (partialAssignment.functions.keySet, partialAssignment.predicates.keySet, partialAssignment.connectors.keySet)
    val (allPatternsFunctions, allPatternsPredicates, allPatternsConnectors, allPatternsFreeVariables, allPatternsBoundVariables) =
      (patternsFunctions ++ otherPatternsFunctions, patternsPredicates ++ otherPatternsPredicates, patternsConnectors ++ otherPatternsConnectors,
        patternsFreeVariables ++ otherPatternsFreeVariables, patternsBoundVariables ++ otherPatternsBoundVariables)
    val valuesVariables = valuesFreeVariables ++ valuesBoundVariables
    val allPatternsVariables = allPatternsFreeVariables ++ allPatternsBoundVariables

    // TODO: do we need to exclude the arguments from these sets?
    val allValuesFunctions = valuesFunctions ++ partialAssignment.functions.values.flatMap { f => schematicTermLabelsOf(f.body) } ++
      (partialAssignment.predicates.values ++ partialAssignment.connectors.values).flatMap { f => schematicTermLabelsOf(f.body) }
    val allValuesPredicates = valuesPredicates ++
      (partialAssignment.predicates.values ++ partialAssignment.connectors.values).flatMap { f => schematicPredicatesOf(f.body) }
    val allValuesConnectors = valuesConnectors ++
      (partialAssignment.predicates.values ++ partialAssignment.connectors.values).flatMap { f => schematicConnectorsOf(f.body) }
    val allValuesVariables = valuesVariables ++ partialAssignment.functions.values.flatMap { f => freeVariablesOf(f.body) } ++
      (partialAssignment.predicates.values ++ partialAssignment.connectors.values).flatMap { f => freeVariablesOf(f.body) ++ declaredBoundVariablesOf(f.body) }

    val (nonUnifiableFunctions, nonUnifiablePredicates, nonUnifiableConnectors) =
      (otherPatternsFunctions.diff(patternsFunctions), otherPatternsPredicates.diff(patternsPredicates), otherPatternsConnectors.diff(patternsConnectors))

    lazy val noInvalidSizeRange = patterns.size == values.size && patterns.size == formulaIndices.size && patterns.zip(formulaIndices).zip(values).forall {
      case ((PartialSequent(leftPattern, rightPattern, _, _), (leftIndices, rightIndices)), Sequent(leftValue, rightValue)) =>
        def check(pattern: IndexedSeq[Formula], indices: IndexedSeq[Int], value: IndexedSeq[Formula]): Boolean =
          pattern.size == indices.size && indices.forall(value.indices.contains)
        check(leftPattern, leftIndices, leftValue) && check(rightPattern, rightIndices, rightValue)
    }
    lazy val noMalformedValues = values.forall(isSequentWellFormed)
    lazy val noSchematicConnectorsValues = values.flatMap(schematicConnectorsOfSequent).isEmpty
    lazy val noMalformedAssignment = // TODO some of these should be a contract in `UnificationContext`
      partialAssignment.functions.values.forall(lambda => isWellFormed(lambda.body)) &&
        partialAssignment.predicates.values.forall(lambda => isWellFormed(lambda.body) && schematicConnectorsOf(lambda.body).isEmpty) &&
        partialAssignment.connectors.values.forall(lambda => isWellFormed(lambda.body) && schematicConnectorsOf(lambda.body).isEmpty)
    lazy val noDeclaredUnknown =
      partialAssignedFunctions.subsetOf(allPatternsFunctions) &&
        partialAssignedPredicates.subsetOf(allPatternsPredicates) &&
        partialAssignedConnectors.subsetOf(allPatternsConnectors)
    lazy val noUndeclaredNonUnifiable =
      nonUnifiableFunctions.subsetOf(partialAssignedFunctions) &&
        nonUnifiablePredicates.subsetOf(partialAssignedPredicates) &&
        nonUnifiableConnectors.subsetOf(partialAssignedConnectors)

    val allRequirements =
      isLegalPatterns(patterns) && isLegalPatterns(otherPatterns) &&
        noInvalidSizeRange && noMalformedValues && noSchematicConnectorsValues && noMalformedAssignment &&
        noDeclaredUnknown && noUndeclaredNonUnifiable

    if(allRequirements) {
      // All requirements are satisfied, we can proceed
      // We must rename the symbols in the pattern such that they are distinct from the ones in the values

      // All the names that are already taken (for simplicity we rename everything)
      val initialTakenFunctions: Set[SchematicTermLabel[?]] =
        patternsFunctions ++ otherPatternsFunctions ++ allValuesFunctions
      val initialTakenPredicates: Set[SchematicPredicateLabel[?]] =
        patternsPredicates ++ otherPatternsPredicates ++ allValuesPredicates
      val initialTakenConnectors: Set[SchematicConnectorLabel[?]] =
        patternsConnectors ++ otherPatternsConnectors ++ allValuesConnectors
      val initialTakenVariables: Set[VariableLabel] = // Free and bound
        patternsFreeVariables ++ patternsBoundVariables ++ otherPatternsFreeVariables ++ otherPatternsBoundVariables ++ allValuesVariables

      def freshMapping[T <: LabelType](taken: Set[T], toRename: Set[T], constructor: (T, String) => T): Map[T, T] = {
        val (finalMap, _) = toRename.foldLeft((Map.empty[T, T], taken.map(_.id))) { case ((map, currentTaken), oldSymbol) =>
          val newName = freshId(currentTaken, oldSymbol.id)
          val newSymbol = constructor(oldSymbol, newName)
          (map + (oldSymbol -> newSymbol), currentTaken + newName)
        }
        finalMap
      }

      // TODO rename variables args

      val functionsFreshMapping = freshMapping(initialTakenFunctions, allPatternsFunctions, (label, newName) => SchematicTermLabel.unsafe(newName, label.arity))
      val predicatesFreshMapping = freshMapping(initialTakenPredicates, allPatternsPredicates, (label, newName) => SchematicPredicateLabel.unsafe(newName, label.arity))
      val connectorsFreshMapping = freshMapping(initialTakenConnectors, allPatternsConnectors, (label, newName) => SchematicConnectorLabel.unsafe(newName, label.arity))
      val variablesFreshMapping = freshMapping(initialTakenVariables, allPatternsFreeVariables ++ allPatternsBoundVariables, (_, newName) => VariableLabel(newName))

      val (functionsInverseMapping, predicatesInverseMapping, connectorsInverseMapping, variablesInverseMapping) =
        (functionsFreshMapping.map(_.swap), predicatesFreshMapping.map(_.swap), connectorsFreshMapping.map(_.swap), variablesFreshMapping.map(_.swap))

      val renamedPartialAssignment = UnificationContext(
        partialAssignment.predicates.map { case (k, v) => predicatesFreshMapping.getOrElse(k, k) -> v },
        partialAssignment.functions.map { case (k, v) => functionsFreshMapping.getOrElse(k, k) -> v },
        partialAssignment.connectors.map { case (k, v) => connectorsFreshMapping.getOrElse(k, k) -> v },
        partialAssignment.variables.map { case (k, v) => variablesFreshMapping.getOrElse(k, k) -> v },
      )

      def rename(patterns: IndexedSeq[PartialSequent]): IndexedSeq[PartialSequent] = {
        def renameFormula(formula: Formula): Formula =
          instantiateFormulaSchemas(
            unsafeRenameVariables(formula, variablesFreshMapping),
            functions = functionsFreshMapping.map { case (k, v) => RenamedLabel.unsafe(k, v).toAssignment }.toSeq,
            predicates = predicatesFreshMapping.map { case (k, v) => RenamedLabel.unsafe(k, v).toAssignment }.toSeq,
            connectors = connectorsFreshMapping.map { case (k, v) => RenamedLabel.unsafe(k, v).toAssignment }.toSeq,
          )
        def renameFormulas(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] = formulas.map(renameFormula)
        patterns.map(p => p.copy(left = renameFormulas(p.left), right = renameFormulas(p.right)))
      }

      val (renamedPatterns, renamedOtherPatterns) = (rename(patterns), rename(otherPatterns))

      val orderedValues = values.zip(formulaIndices).flatMap { case (value, (indicesLeft, indicesRight)) =>
        indicesLeft.map(value.left) ++ indicesRight.map(value.right)
      }

      val constraints = collect(renamedPatterns.flatMap(_.formulas).zip(orderedValues), valuesFunctions, valuesPredicates, valuesConnectors, valuesVariables)

      val unified = constraints
        .flatMap(unifyFromConstraints(_, renamedPartialAssignment, allValuesFunctions, allValuesPredicates, allValuesConnectors, allValuesVariables))
        .filter(assignment => // Check if the assignment is full (should this be an assertion?)
          assignment.functions.keySet.map(functionsInverseMapping) == allPatternsFunctions &&
            assignment.predicates.keySet.map(predicatesInverseMapping) == allPatternsPredicates &&
            assignment.connectors.keySet.map(connectorsInverseMapping) == allPatternsConnectors &&
            assignment.variables.keySet.map(variablesInverseMapping) == allPatternsVariables
        )

      unified.map { renamedAssignment =>
        val assignment = UnificationContext(
          renamedAssignment.predicates.map { case (k, v) => predicatesInverseMapping.getOrElse(k, k) -> v },
          renamedAssignment.functions.map { case (k, v) => functionsInverseMapping.getOrElse(k, k) -> v },
          renamedAssignment.connectors.map { case (k, v) => connectorsInverseMapping.getOrElse(k, k) -> v },
          renamedAssignment.variables.map { case (k, v) => variablesInverseMapping.getOrElse(k, k) -> v },
        )

        // Union all
        val otherValues = inflateValues(renamedOtherPatterns, values, renamedAssignment, formulaIndices)

        (otherValues, assignment)
      }
    } else {
      None
    }
  }

  type SequentSelector = (IndexedSeq[Int], IndexedSeq[Int])

  /**
   * A helper method designed to enumerate all possible correspondences between patterns and values.
   * @param map an optional partial correspondence (or empty if none)
   * @param patterns the patterns
   * @param values the values
   * @return a lazy list of correspondences
   */
  def matchIndices(map: Map[Int, SequentSelector], patterns: IndexedSeq[PartialSequent], values: IndexedSeq[Sequent]): View[IndexedSeq[SequentSelector]] = {
    require(patterns.size == values.size)
    // Normally `pattern` shouldn't be empty, but this function works regardless
    if(map.keySet.forall(patterns.indices.contains)) {
      val selectors = patterns.indices.map(map.getOrElse(_, (IndexedSeq.empty, IndexedSeq.empty)))
      selectors.zip(patterns.zip(values)).map { case ((leftSelector, rightSelector), (pattern, value)) =>
        def enumerate(selectorSide: IndexedSeq[Int], patternSideSize: Int, isPatternPartial: Boolean, valueSide: Range): View[IndexedSeq[Int]] = {
          // TODO remove the partial parameter as it is not needed in this direction
          if(selectorSide.isEmpty) { // If empty we consider all permutations
            // If `valueSide` is empty then it will produce an empty array
            valueSide.combinations(patternSideSize).flatMap(_.permutations).toSeq.view
          } else {
            if(selectorSide.size == patternSideSize) {
              if(selectorSide.forall(valueSide.contains)) {
                // We return exactly what was selected
                View(selectorSide)
              } else {
                // An index value is out of range
                View.empty
              }
            } else {
              // Number of args does not match the pattern's
              View.empty
            }
          }
        }
        val leftSide = enumerate(leftSelector, pattern.left.size, pattern.partialLeft, value.left.indices)
        val rightSide = enumerate(rightSelector, pattern.right.size, pattern.partialRight, value.right.indices)
        for {
          l <- leftSide
            r <- rightSide
        } yield IndexedSeq((l, r))
      }.fold(View(IndexedSeq.empty[(IndexedSeq[Int], IndexedSeq[Int])])) { case (v1, v2) =>
        for {
          first <- v1
            second <- v2
        } yield first ++ second
      }
    } else {
      // Map contains values outside the range
      View.empty
    }
  }

}
