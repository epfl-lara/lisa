package lisa.settheory

import lisa.prooflib.Library

/**
 * Specific implementation of [[utilities.Library]] for Set Theory, with a RunningTheory that is supposed to be used by the standard library.
 */
object SetTheoryLibrary extends SetTheoryTGAxioms {
  export lisa.fol.FOL.{*, given}
  // Unicode symbols

  val ∅ = emptySet
  val ∈ = in

  extension (thi: Term) {
    def ∈(that: Term): Formula = in(thi, that)
    def ⊆(that: Term): Formula = subset(thi, that)

    def =/=(that: Term): Formula = !(===(thi, that))

  }

}
