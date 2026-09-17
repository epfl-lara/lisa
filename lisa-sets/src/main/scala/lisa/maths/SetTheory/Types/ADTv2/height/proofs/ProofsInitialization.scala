package lisa.maths.SetTheory.Types.ADTv2.height.proofs


object ProofsInitialization {

  def initialize(): Unit = {
    CoreFacts.initialize()
    SuccessorFacts.initialize()
    UniquenessFacts.initialize()
  }
}
