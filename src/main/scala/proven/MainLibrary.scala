package proven

import lisa.kernel.proof.RunningTheory
import lisa.settheory.AxiomaticSetTheory
import lisa.settheory.SetTheoryDefinitions
import utilities.Library

abstract class MainLibrary extends Library(AxiomaticSetTheory.runningSetTheory) with SetTheoryDefinitions {
  import AxiomaticSetTheory.*
  override val realOutput: String => Unit = println

}
