package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.utils.Printer

/**
 * Some higher level construct definitions for Set Theory library
 */
trait BasicDefs extends lisa.Main {

  // my stupid defs
  def properSubset(x: Term, y: Term) = subset(x, y) /\ !(x === y)
  def singleton(x: Term) = unorderedPair(x, x)
  def pair(x: Term, y: Term) = unorderedPair(unorderedPair(x, y), singleton(x))

}
