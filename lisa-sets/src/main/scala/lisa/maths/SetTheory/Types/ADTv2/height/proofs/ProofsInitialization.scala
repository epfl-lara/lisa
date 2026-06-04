package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Types.ADTv2.support.Time

object ProofsInitialization {

  def initialize(): Unit = Time.measure("Height proofs initialization") {
    CoreFacts.initialize()
    SuccessorFacts.initialize()
    UniquenessFacts.initialize()
  }
}
