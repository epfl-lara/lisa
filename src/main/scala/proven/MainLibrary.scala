package proven

import lisa.kernel.proof.RunningTheory
import lisa.settheory.AxiomaticSetTheory
import lisa.settheory.SetTheoryTGAxioms
import utilities.Library

abstract class MainLibrary extends Library(AxiomaticSetTheory.runningSetTheory) with SetTheoryTGAxioms {
  import AxiomaticSetTheory.*
  override val output: String => Unit = println

}
