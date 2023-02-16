package lisa.test

import lisa.prooflib.Library

object TestTheoryLibrary extends Library {
  val theory: TestTheory.runningTestTheory.type = TestTheory.runningTestTheory
  export TestTheory.*
}
