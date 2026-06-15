package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.SetTheory._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Pointwise uniqueness of solutions to the function's defining predicate.
 *
 * Proved by direct case coverage in the non-recursive case
 * ([[lisa.maths.SetTheory.Types.ADTv2.functions.Uniqueness]]) and by
 * well-founded induction on height in the recursive case
 * ([[lisa.maths.SetTheory.Types.ADTv2.recursion.Uniqueness]]).
 */
trait UniquenessProof[N <: Arity] {

  /** `Def[f:=x] /\ Def[f:=y] ==> (x === y)` — any two solutions agree. */
  def pointwiseUniqueness: THM
}
