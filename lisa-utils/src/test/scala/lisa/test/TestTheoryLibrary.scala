package lisa.test

import lisa.prooflib.Library

object TestTheoryLibrary extends Library(TestTheory.runningTestTheory) {
  export TestTheory.*
}
