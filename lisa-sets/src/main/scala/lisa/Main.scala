package lisa

import lisa.prooflib.BasicMain
import lisa.SetTheoryLibrary

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {
 
  export lisa.fol.FOL.{*, given}
  export SetTheoryLibrary.{given, _}
  export lisa.prooflib.BasicStepTactic.*
  export lisa.prooflib.SimpleDeducedSteps.*

  export lisa.automation.kernel.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau

  knownDefs.update(emptySet, Some(emptySetAxiom))
  knownDefs.update(unorderedPair, Some(pairAxiom))
  knownDefs.update(union, Some(unionAxiom))
  knownDefs.update(powerSet, Some(powerAxiom))
  knownDefs.update(subset, Some(subsetAxiom))


  extension (symbol: ConstantLabel[?]) {
    def definition: JUSTIFICATION = {
      getDefinition(symbol).get
    }
  }


}
