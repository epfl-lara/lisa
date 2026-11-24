package lisa.maths.SetTheory.Types.ADT.height.proofs

object ProofsInitialization {

  def initialize(): Unit = {
    CoreFacts.initialize()
    SuccessorFacts.initialize()
    UniquenessFacts.initialize()
  }
}
