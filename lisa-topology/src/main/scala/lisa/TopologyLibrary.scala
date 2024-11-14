package lisa

import lisa.fol.FOL.{_, given}
import lisa.kernel.proof.RunningTheory
import lisa.prooflib.Library

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object TopologyLibrary extends lisa.prooflib.Library {

  val theory = new RunningTheory()
  final val T = variable

  // Predicates
  /**
   * The symbol for the set membership predicate.
   */
  final val isTopology = ConstantPredicateLabel("isTopology", 1)
  
  final val WhatTopologyIs: Formula = forall(T, isTopology(T))

  private val peanoAxioms: Set[(String, Formula)] = Set(
    ("ax1ZeroSuccessor", WhatTopologyIs),
  )
  peanoAxioms.foreach(a => theory.addAxiom(a._1, a._2.underlying))

}
