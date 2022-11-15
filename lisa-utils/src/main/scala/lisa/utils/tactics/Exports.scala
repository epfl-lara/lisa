package lisa.utils.tactics

import lisa.utils.tactics.BasicStepTactic.*
import lisa.kernel.fol.FOL.*
//import lisa.utils.tactics.SimpleDeducedSteps.Restate
import lisa.utils.Helpers.{*, given}
import lisa.utils.{Library, LisaException, OutputManager}

object Exports {
  export lisa.utils.tactics.BasicStepTactic.*
  export lisa.utils.tactics.SimpleDeducedSteps.*
}
