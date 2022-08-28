package lisa.test

import lisa.utils.Library

object TestTheoryLibrary extends Library(TestTheory.runningTestTheory) {
  export TestTheory.*
}
