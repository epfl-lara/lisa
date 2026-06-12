package lisa.maths.SetTheory.Types.ADTv2.recursion.proofs

import lisa.maths.SetTheory.Types.ADTv2.support.Time

object ProofsInitialization {

  def initialize(): Unit = Time.measure("Rec proofs initialization") {
    LimitKernel.initialize()
    ApproximationChainFacts.initialize()
    WitnessCaseExtensionality.initialize()
  }
}
