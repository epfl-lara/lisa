package lisa

import lisa.SetTheoryLibrary
import lisa.utils.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {

  export lisa.utils.fol.FOL.{*, given}
  export SetTheoryLibrary.{given, _}
  export lisa.utils.prooflib.BasicStepTactic.*
  export lisa.utils.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution.{Apply as Substitute}
  export lisa.automation.Tableau
  export lisa.automation.Congruence
  // export lisa.automation.Apply
  // export lisa.automation.Exact

  knownDefs.update(∅, Some(emptySetAxiom))
  knownDefs.update(unorderedPair, Some(pairAxiom))
  knownDefs.update(⋃, Some(unionAxiom))
  knownDefs.update(power, Some(powerSetAxiom))
  knownDefs.update(⊆, Some(subsetAxiom))

  extension (symbol: Constant[?]) {
    def definition: JUSTIFICATION = {
      getDefinition(symbol).get
    }
    def shortDefinition: JUSTIFICATION = {
      getShortDefinition(symbol).get
    }
  }

}
