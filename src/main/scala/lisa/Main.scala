package lisa

import lisa.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {
  export lisa.settheory.SetTheoryLibrary.{given, _}
  export lisa.prooflib.Exports.*

  knownDefs.update(emptySet, Some(emptySetAxiom))
  knownDefs.update(unorderedPair, Some(pairAxiom))
  knownDefs.update(union, Some(unionAxiom))
  knownDefs.update(powerSet, Some(powerAxiom))
  knownDefs.update(subset, Some(subsetAxiom))



  //TOFO: Refine errors and messages
  extension (symbol: ConstantLabel[?]) {
    def definition: JUSTIFICATION = symbol match {
      case `equality` => throw new NoSuchElementException("Equality has no definition")
      case `top` => throw new NoSuchElementException("Top has no definition")
      case `bot` => throw new NoSuchElementException("Bot has no definition")
      case `in` => throw new NoSuchElementException("Membership has no definition")
      case _ => getDefinition(symbol).get
        
    }
  }
}
