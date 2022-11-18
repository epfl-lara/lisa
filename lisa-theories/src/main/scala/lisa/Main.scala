package lisa

import lisa.utils.BasicMain
import lisa.utils.OutputManager

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {
  export lisa.settheory.SetTheoryLibrary.{_, given}
}
