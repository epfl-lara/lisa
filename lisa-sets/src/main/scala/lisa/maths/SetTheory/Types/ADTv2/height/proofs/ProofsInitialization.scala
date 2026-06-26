package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.utils.debug.Time

object ProofsInitialization {

  def initialize(): Unit = Time.measure("Height proofs initialization") {
    CoreFacts.initialize()
    SuccessorFacts.initialize()
    UniquenessFacts.initialize()
  }
}
