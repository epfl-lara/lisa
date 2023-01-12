package lisa

import lisa.prooflib.BasicMain
import lisa.prooflib.OutputManager

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {
  export lisa.settheory.SetTheoryLibrary.{_, given}
}
