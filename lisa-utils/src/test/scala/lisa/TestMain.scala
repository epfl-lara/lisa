package lisa

import lisa.test.TestTheoryLibrary

trait TestMain {

  export TestTheoryLibrary.{*, given}
  export lisa.utils.prooflib.BasicStepTactic.*
  export lisa.utils.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution.{Apply as Substitute}
  export lisa.automation.Tableau
  export lisa.automation.Congruence

}
