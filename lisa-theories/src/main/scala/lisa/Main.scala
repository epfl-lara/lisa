package lisa

import lisa.prooflib.BasicMain
import lisa.prooflib.OutputManager
import lisa.utils.LisaException

import java.util

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {
  export lisa.settheory.SetTheoryLibrary.{_, given}

  extension (symbol: ConstantFunctionLabel) {
    def definition: theory.Justification = symbol match {
      case `emptySet` => emptySetAxiom
      case `unorderedPair` => pairAxiom
      case `union` => unionAxiom
      case `powerSet` => powerAxiom
      case _ =>
        theory.getDefinition(symbol.id) match {
          case Some(value) => value
          case None => throw new NoSuchElementException(s"${symbol.id} has not been defined in the current theory")
        }
    }
  }

  extension (symbol: ConstantPredicateLabel) {
    def definition: theory.Justification = symbol match {
      case `equality` => throw new NoSuchElementException("Equality has no definition")
      case `top` => throw new NoSuchElementException("Top has no definition")
      case `bot` => throw new NoSuchElementException("Bot has no definition")
      case `in` => throw new NoSuchElementException("Membership has no definition")
      case `subset` => subsetAxiom
      case _ =>
        theory.getDefinition(symbol.id) match {
          case Some(value) => value
          case None => throw new NoSuchElementException(s"${symbol.id} has not been defined in the current theory")
        }
    }
  }
}
