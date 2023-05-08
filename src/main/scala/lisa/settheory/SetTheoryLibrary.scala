package lisa.settheory

import lisa.kernel.fol.FOL
import lisa.prooflib.Library

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object SetTheoryLibrary extends Library with SetTheoryTGAxioms {
  export lisa.prooflib.Exports.*

export lisa.kernel.fol.FOL.*
  val theory: runningSetTheory.type = runningSetTheory

  // Unicode symbols

  val ∅ : Term = emptySet()
  extension (t: Term) {
    infix def ∈(u: Term): Formula = PredicateFormula(in, Seq(t, u))
  }

}
