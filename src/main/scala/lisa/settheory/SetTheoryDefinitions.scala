package lisa.settheory

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.RunningTheory
import lisa.KernelHelpers.{given, _}
/**
 * Base trait for set theoretical axiom systems.
 * Defines the symbols used in set theory.
 */
private[settheory] trait SetTheoryDefinitions{
  type Axiom = Formula
  def axioms: Set[Axiom] = Set.empty
  private[settheory] final val (x, y, z, a, b) =
    (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"), VariableLabel("A"), VariableLabel("B"))
  final val sPhi = SchematicPredicateLabel("P", 2)
  final val sPsi = SchematicPredicateLabel("P", 3)
  // Predicates
  final val in: PredicateLabel = ConstantPredicateLabel("set_membership", 2)
  final val subset: PredicateLabel = ConstantPredicateLabel("subset_of", 2)
  final val sim: PredicateLabel = ConstantPredicateLabel("same_cardinality", 2) // Equicardinality
  final val predicates = Set(in, subset, sim)
  // val application
  // val pick

  // Functions
  final val emptySet: FunctionLabel = ConstantFunctionLabel("empty_set", 0)
  final val pair: FunctionLabel = ConstantFunctionLabel("unordered_pair", 2)
  final val singleton: FunctionLabel = ConstantFunctionLabel("singleton", 1)
  final val powerSet: FunctionLabel = ConstantFunctionLabel("power_set", 1)
  final val union: FunctionLabel = ConstantFunctionLabel("union", 1)
  final val universe: FunctionLabel = ConstantFunctionLabel("universe", 1)
  final val functions = Set(emptySet, pair, singleton, powerSet, union, universe)

  val runningSetTheory:RunningTheory = new RunningTheory()
  given RunningTheory = runningSetTheory

  predicates.foreach(s => runningSetTheory.addSymbol(s))
  functions.foreach(s => runningSetTheory.addSymbol(s))
}