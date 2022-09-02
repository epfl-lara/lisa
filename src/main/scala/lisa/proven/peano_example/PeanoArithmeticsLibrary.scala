package lisa.proven.peano_example

object PeanoArithmeticsLibrary extends lisa.utils.Library(lisa.proven.peano_example.PeanoArithmetics.runningPeanoTheory) {
  export lisa.proven.peano_example.PeanoArithmetics.*
}
