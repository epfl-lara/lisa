package proven.dev

import lisa.kernel.proof.RunningTheory
import lisa.settheory.AxiomaticSetTheory

trait MainLibrary {

  given RunningTheory = AxiomaticSetTheory.runningSetTheory
  import AxiomaticSetTheory.runningSetTheory.*

}
