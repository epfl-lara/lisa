package lisa

import lisa.SetTheoryLibrary
import lisa.utils.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {

  export lisa.utils.fol.FOL.{=== as _, ≠ as _, *, given}
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
  knownDefs.update(𝒫, Some(powerSetAxiom))
  knownDefs.update(⊆, Some(subsetAxiom))

}
