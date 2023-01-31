package lisa.proven.peano_example

object PeanoArithmeticsLibrary extends lisa.prooflib.Library(lisa.proven.peano_example.PeanoArithmetics.runningPeanoTheory) {
  export lisa.proven.peano_example.PeanoArithmetics.*
}
