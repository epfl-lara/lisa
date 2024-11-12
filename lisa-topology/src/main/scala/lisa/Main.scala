package lisa

import lisa.SetTheoryLibrary
import lisa.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {

  export lisa.fol.FOL.{*, given}
  export SetTheoryLibrary.{given, _}
  export lisa.prooflib.BasicStepTactic.*
  export lisa.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau
  export lisa.automation.Apply
  export lisa.automation.Exact

  knownDefs.update(emptySet, Some(emptySetAxiom))
  knownDefs.update(unorderedPair, Some(pairAxiom))
  knownDefs.update(union, Some(unionAxiom))
  knownDefs.update(powerSet, Some(powerAxiom))
  knownDefs.update(subset, Some(subsetAxiom))

  extension (symbol: ConstantLabel[?]) {
    def definition: JUSTIFICATION = {
      getDefinition(symbol).get
    }
    def shortDefinition: JUSTIFICATION = {
      getShortDefinition(symbol).get
    }
  }

}
