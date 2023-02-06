package lisa.settheory

import lisa.prooflib.Library

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object SetTheoryLibrary extends Library with SetTheoryTGAxioms  {
  export lisa.prooflib.Exports.*
  val theory: runningSetTheory.type = runningSetTheory





}
