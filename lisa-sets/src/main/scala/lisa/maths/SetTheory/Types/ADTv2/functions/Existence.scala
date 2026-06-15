package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.ExistenceProof
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
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

  private val witnessDefinition: Expr[Prop] =
    spec.untypedDefinition(witness.witness)

  private val witnessCases: Expr[Prop] =
    simplify(
      seqAnd(
        spec.cases.map(pattern =>
          forallSeq(
            pattern.binders,
            pattern.branchPremise ==> (witness.witness * pattern.inputTerm === pattern.body)
          )
        )
      )
    )

  /**
   * ∃f, Def(f)
   */
  val witnessExists: THM = Lemma(∃(f, spec.untypedDefinition(f))) {
    val patternCaseFacts = spec.cases.map(pattern => witness.witnessCaseByPattern(pattern))
    have(witnessCases) by Tautology.from(patternCaseFacts*)
    have(witnessDefinition) by Tautology.from(lastStep, witness.witnessHasType)
    thenHave(∃(f, spec.untypedDefinition(f))) by RightExists
  }
}
