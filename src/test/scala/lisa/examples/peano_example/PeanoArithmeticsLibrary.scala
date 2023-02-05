package lisa.examples.peano_example

import lisa.examples.peano_example

object PeanoArithmeticsLibrary extends lisa.prooflib.Library(peano_example.PeanoArithmetics.runningPeanoTheory) {
  export PeanoArithmetics.*
}
