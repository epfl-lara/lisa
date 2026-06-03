package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{Pattern, PatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Shared semantic witness construction for ADTv2 functions.
 *
 * A case-defined witness is a relation `W ⊆ A × T` described by semantic branches.
 * This class factors the common proof layer used by ordinary semantic
 * functions and recursive witness relations:
 *   - branch-wise witness membership
 *   - relation-betweenness
 *   - totality and single-valuedness
 *   - uniqueness of outputs
 *   - function typing
 *   - witness application equations on branch inputs
 *
 * Clients provide the ADT-specific ingredients:
 *   - the witness term and its `DEF` equation
 *   - the branch bodies and the `caseMembership` predicate
 *   - return-type checks for each branch body
 *   - optional ambient assumptions required to type the branch bodies
 *
 * When `contextPremises` is empty, exported theorems are plain formulas. When it is
 * non-empty, theorems are wrapped under the conjunction of these premises.
 */
final class CaseDefinedWitness[N <: Arity](
    protected val adt: SemanticADT[N],
    protected val argType: Expr[Ind],
    protected val patternMatching: PatternSystem[N],
    protected val returnType: Expr[Ind],
    protected val typ: Expr[Ind],
    protected val witness: Expr[Ind],
    protected val witnessDef: JUSTIFICATION,
    protected val witnessBound: Expr[Ind],
    protected val pairWitness: Variable[Ind],
    protected val caseMembership: Expr[Ind] => Expr[Prop],
    protected val checkReturnType: Map[Pattern[N], JUSTIFICATION],
    protected val constructorTagDisequalities: Map[(SemanticConstructor[N], SemanticConstructor[N]), THM],
    protected val contextPremises: Seq[Expr[Prop]] = Seq.empty
) extends WitnessApplicationProofs[N]
