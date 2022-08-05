package lisa.proven

object PeanoArithmeticsLibrary extends lisa.utils.Library(lisa.proven.mathematics.PeanoArithmetics.runningPeanoTheory) {
  export lisa.proven.mathematics.PeanoArithmetics.*
}
