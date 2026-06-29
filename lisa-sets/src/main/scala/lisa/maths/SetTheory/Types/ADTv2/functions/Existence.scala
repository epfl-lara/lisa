package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.ExistenceProof
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Existence of a solution.
 *
 * Mirror of [[lisa.maths.SetTheory.Types.ADTv2.recursion.Existence]], but
 * trivial: with no self-reference the witness set [[Witness.witness]] is itself
 * a solution, so `∃f. Def(f)` follows by a single `RightExists` — no
 * approximant/limit fixpoint construction is needed.
 */
private[functions] final class Existence[N <: Arity](
    spec: FunSpec[N],
    witness: Witness[N]
) extends ExistenceProof[N] {

  /**
   * ∃f, Def(f)
   */
  val witnessExists: THM = Lemma(∃(f, spec.definitionAt(f))) {
    val patternCaseFacts = spec.cases.map(pattern => witness.witnessCaseByPattern(pattern))
    have(spec.equationConstraint(witness.witness)) by Tautology.from(patternCaseFacts*)
    have(spec.definitionAt(witness.witness)) by RightAnd(lastStep, witness.witnessHasType)
    thenHave(∃(f, spec.definitionAt(f))) by RightExists
  }
}
