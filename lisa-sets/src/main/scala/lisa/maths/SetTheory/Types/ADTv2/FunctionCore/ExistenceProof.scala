package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.SetTheory._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Existence of a solution to the function's defining predicate.
 *
 * Proved trivially in the non-recursive case (the witness set is itself a
 * solution, [[lisa.maths.SetTheory.Types.ADTv2.functions.Existence]]) and via
 * the approximant/limit fixpoint construction in the recursive case
 * ([[lisa.maths.SetTheory.Types.ADTv2.recursion.Existence]]).
 */
trait ExistenceProof[N <: Arity] {

  /** `∃f, Def(f)` — some `f` satisfies the function's defining predicate. */
  def witnessExists: THM
}
