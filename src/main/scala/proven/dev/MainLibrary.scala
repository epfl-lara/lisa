package proven.dev

import lisa.kernel.proof.RunningTheory
import lisa.settheory.AxiomaticSetTheory

trait MainLibrary extends Library {
  implicit val theory: RunningTheory = AxiomaticSetTheory.runningSetTheory
  
  import AxiomaticSetTheory.runningSetTheory.*

}
