package lisa.front.proof.unification

import lisa.front.fol.FOL.*

trait UnificationDefinitions {

  /**
   * An assignment for a unification problem instance.
   * @param predicates the assigned predicates
   * @param functions the assigned functions
   * @param connectors the assigned connectors
   * @param variables the assigned variables
   */
  case class UnificationContext(
    predicates: Map[SchematicPredicateLabel[?], LambdaPredicate[?]] = Map.empty,
    functions: Map[SchematicTermLabel[?], LambdaFunction[?]] = Map.empty,
    connectors: Map[SchematicConnectorLabel[?], LambdaConnector[?]] = Map.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  ) {
    infix def +(predicate: AssignedPredicate): UnificationContext = copy(predicates = predicates + (predicate.schema -> predicate.lambda))
    infix def +(function: AssignedFunction): UnificationContext = copy(functions = functions + (function.schema -> function.lambda))
    infix def +(connector: AssignedConnector): UnificationContext = copy(connectors = connectors + (connector.schema -> connector.lambda))
    infix def +(pair: (VariableLabel, VariableLabel)): UnificationContext = copy(functions = functions + (pair._1 -> pair._2))

    def apply[N <: Arity](predicate: SchematicPredicateLabel[N]): LambdaPredicate[N] = predicates(predicate).asInstanceOf[LambdaPredicate[N]]
    def apply[N <: Arity](function: SchematicTermLabel[N]): LambdaFunction[N] = functions(function).asInstanceOf[LambdaFunction[N]]
    def apply[N <: Arity](connector: SchematicConnectorLabel[N]): LambdaConnector[N] = connectors(connector).asInstanceOf[LambdaConnector[N]]

    def apply(predicate: SchematicPredicateLabel[0]): Formula = predicates(predicate).body
    def apply(function: SchematicTermLabel[0]): Term = functions(function).body
    

    def assignedPredicates: Seq[AssignedPredicate] = predicates.map { case (k, v) => AssignedPredicate.unsafe(k, v) }.toSeq
    def assignedFunctions: Seq[AssignedFunction] = functions.map { case (k, v) => AssignedFunction.unsafe(k, v) }.toSeq
    def assignedConnectors: Seq[AssignedConnector] = connectors.map { case (k, v) => AssignedConnector.unsafe(k, v) }.toSeq
  }

  /**
   * A helper object that represents a renaming.
   * @param predicates the renamed predicates
   * @param functions the renamed functions
   * @param connectors the renamed connectors
   * @param variables the renamed free variables
   */
  case class RenamingContext(
    predicates: Seq[RenamedPredicateSchema] = Seq.empty,
    functions: Seq[RenamedFunctionSchema] = Seq.empty,
    connectors: Seq[RenamedConnectorSchema] = Seq.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  )

}
