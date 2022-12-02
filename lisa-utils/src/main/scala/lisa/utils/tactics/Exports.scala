package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.utils.Helpers.{_, given}
import lisa.utils.Library
import lisa.utils.LisaException
import lisa.utils.OutputManager
import lisa.utils.tactics.BasicStepTactic.*

object Exports {
  export lisa.utils.tactics.BasicStepTactic.*
  export lisa.utils.tactics.SimpleDeducedSteps.*
}
