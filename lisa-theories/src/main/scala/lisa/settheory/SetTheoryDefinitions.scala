package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.Helpers.{_, given}

/**
 * Base trait for set theoretical axiom systems.
 * Defines the symbols used in set theory.
 */
private[settheory] trait SetTheoryDefinitions {

  def axioms: Set[(String, Formula)] = Set.empty

  // Predicates
  /**
   * The symbol for the set membership predicate.
   */
  final val in = ConstantPredicateLabel("elem", 2)

  /**
   * The symbol for the subset predicate.
   */
  final val subset = ConstantPredicateLabel("subsetOf", 2)

  /**
   * The symbol for the equicardinality predicate. Needed for Tarski's axiom.
   */
  final val sim = ConstantPredicateLabel("sameCardinality", 2) // Equicardinality
  /**
   * Set Theory basic predicates
   */
  final val predicates = Set(in, subset, sim)
  // val choice

  // Functions
  /**
   * The symbol for the empty set constant.
   */
  final val emptySet = ConstantFunctionLabel("emptySet", 0)

  /**
   * The symbol for the unordered pair function.
   */
  final val unorderedPair = ConstantFunctionLabel("unorderedPair", 2)

  /**
   * The symbol for the powerset function.
   */
  final val powerSet = ConstantFunctionLabel("powerSet", 1)

  /**
   * The symbol for the set union function.
   */
  final val union = ConstantFunctionLabel("union", 1)

  /**
   * The symbol for the universe function. Defined in TG set theory.
   */
  final val universe = ConstantFunctionLabel("universe", 1)

  /**
   * Set Theory basic functions.
   */
  final val functions = Set(emptySet, unorderedPair, powerSet, union, universe)

  /**
   * The kernel theory loaded with Set Theory symbols and axioms.
   */
  val runningSetTheory: RunningTheory = new RunningTheory()
  // given RunningTheory = runningSetTheory

  predicates.foreach(s => runningSetTheory.addSymbol(s))
  functions.foreach(s => runningSetTheory.addSymbol(s))
}
