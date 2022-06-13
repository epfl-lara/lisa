package lisa.proven

import lisa.utils.Printer
import lisa.test.ProofCheckerSuite

class InitialProofsTests extends ProofCheckerSuite {
  import lisa.proven.SetTheoryLibrary.*

  test("File SetTheory initialize well") {
    lisa.proven.mathematics.SetTheory
    succeed
  }

  test("File Mapping initialize well") {
    lisa.proven.mathematics.Mapping
    succeed
  }


}
