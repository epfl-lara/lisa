package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Library
import lisa.utils.Printer
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.utils.tactics.BasicStepTactic.*
import lisa.utils.tactics.ProofTacticLib

/**
 * Some higher level construct definitions for Set Theory library
 */
trait BasicDefs extends lisa.Main {
  
  // my stupid defs
  def properSubset(x: Term, y: Term) = subset(x, y) /\ ! (x === y)
  def singleton(x: Term) = unorderedPair(x, x)
  def pair(x: Term, y: Term) = unorderedPair(unorderedPair(x, y), singleton(x))
  
  
}
