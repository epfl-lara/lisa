package lisa.kernel.proof

object TheoremRegistrySnapshot:
  def names(theory: RunningTheory): Set[String] = theory.theorems.keySet.toSet
