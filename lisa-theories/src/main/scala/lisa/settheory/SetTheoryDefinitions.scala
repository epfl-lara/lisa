package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.Helpers.{*, given}

/**
 * Base trait for set theoretical axiom systems.
 * Defines the symbols used in set theory.
 */
private[settheory] trait SetTheoryDefinitions {

  def axioms: Set[(String, Formula)] = Set.empty

  // Predicates
  final val in = ConstantPredicateLabel("set_membership", 2)
  final val subset = ConstantPredicateLabel("subset_of", 2)
  final val sim = ConstantPredicateLabel("same_cardinality", 2) // Equicardinality
  final val predicates = Set(in, subset, sim)
  // val application
  // val pick

  // Functions
  final val emptySet = ConstantFunctionLabel("empty_set", 0)
  final val pair = ConstantFunctionLabel("unordered_pair", 2)
  final val singleton = ConstantFunctionLabel("singleton", 1)
  final val powerSet = ConstantFunctionLabel("power_set", 1)
  final val union = ConstantFunctionLabel("union", 1)
  final val universe = ConstantFunctionLabel("universe", 1)
  final val functions = Set(emptySet, pair, singleton, powerSet, union, universe)

  val runningSetTheory: RunningTheory = new RunningTheory()
  // given RunningTheory = runningSetTheory

  predicates.foreach(s => runningSetTheory.addSymbol(s))
  functions.foreach(s => runningSetTheory.addSymbol(s))
}
