package lisa.settheory

import lisa.utils.Library

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object SetTheoryLibrary extends Library(lisa.settheory.AxiomaticSetTheory.runningSetTheory) {
  val AxiomaticSetTheory: lisa.settheory.AxiomaticSetTheory.type = lisa.settheory.AxiomaticSetTheory
  export AxiomaticSetTheory.*

}
