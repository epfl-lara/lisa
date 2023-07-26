package lisa.settheory

import lisa.prooflib.Library

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object SetTheoryLibrary extends Library{
  /*
  export SetTheoryTGAxioms.runningSetTheory
  export lisa.prooflib.Exports.*
  export F.*
  val theory: runningSetTheory.type = runningSetTheory


  final val in = ConstantPredicateLabel[2]("elem")

  /**
   * The symbol for the subset predicate.
   */
  final val subset = ConstantPredicateLabel[2]("subsetOf")

  /**
   * The symbol for the equicardinality predicate. Needed for Tarski's axiom.
   */
  final val sim = ConstantPredicateLabel[2]("sameCardinality") // Equicardinality
  /**
   * Set Theory basic predicates
   */
  final val predicates = Set(in, subset, sim)
  // val choice

  // Functions
  /**
   * The symbol for the empty set constant.
   */
  final val emptySet = Constant("emptySet")
  val ∅ : Term = emptySet

  /**
   * The symbol for the unordered pair function.
   */
  final val unorderedPair = ConstantFunctionalLabel[2]("unorderedPair")

  /**
   * The symbol for the powerset function.
   */
  final val powerSet = ConstantFunctionalLabel[1]("powerSet")

  /**
   * The symbol for the set union function.
   */
  final val union = ConstantFunctionalLabel[1]("union")

  /**
   * The symbol for the universe function. Defined in TG set theory.
   */
  final val universe = ConstantFunctionalLabel[1]("universe")

  /**
   * Set Theory basic functions.
   */
  final val functions = Set(emptySet, unorderedPair, powerSet, union, universe)

  /**
   * The kernel theory loaded with Set Theory symbols and axioms.
   */
  val runningSetTheory: RunningTheory = new RunningTheory()
  // given RunningTheory = runningSetTheory

  predicates.foreach(s => addSymbol(s))
  functions.foreach(s => addSymbol(s))


  // Unicode symbols

  
  extension (t: Term) {
    infix def ∈(u: Term): Formula = PredicateFormula(in, Seq(t, u))
  }
*/
}
