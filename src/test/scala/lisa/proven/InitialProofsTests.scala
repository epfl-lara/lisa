package lisa.proven

import utilities.Printer
import test.ProofCheckerSuite

class InitialProofsTests extends ProofCheckerSuite {
  import proven.SetTheoryLibrary.*

  test("File SetTheory initialize well") {
    proven.mathematics.SetTheory
    succeed
  }

  test("File Mapping initialize well") {
    proven.mathematics.Mapping
    succeed
  }


}
