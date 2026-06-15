package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.WitnessBase
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Layer 2 — Witness construction.
 *
 * Defines the witness set
 *   W(g) = { p ∈ A×T | caseMembership_g(p) }
 * where `g` = [[spec.selfPlaceholder]] stands for the recursive self-reference.
 *
 * The case-defined witness proof core is shared with ordinary semantic functions
 * through [[CaseDefinedWitness]]. This class keeps only the recursion-specific shell:
 *   - the free self-reference [[spec.selfPlaceholder]]
 *   - the contextual typing premise `selfPlaceholder :: A→T`
 *   - branch return-type checks under that premise
 */
private[recursion] final class Witness[N <: Arity](spec: FunSpec[N])
    extends WitnessBase[N](
      functionName = spec.functionName,
      adt = spec.adt,
      argType = spec.argType,
      patternMatching = spec.patternMatching,
      returnType = spec.returnType,
      typ = spec.typ,
      typeVariablesSeq = spec.typeVariablesSeq
    ) {

  private val selfPlaceholder: Variable[Ind] = spec.selfPlaceholder

  /**
   * typingPremise = selfPlaceholder :: A→T (the induction hypothesis on the self-reference).
   */
  val typingPremise: Expr[Prop] = selfPlaceholder :: spec.typ

  /**
   * Definitional equation for the witness: W(selfPlaceholder) = witnessBody.
   */
  val witnessDef: JUSTIFICATION = witnessDefCore

  def apply(g: Expr[Ind]): Expr[Ind] =
    witness.substitute(spec.selfPlaceholder := g)

  override protected def witnessParametersSeq: Seq[Variable[Ind]] =
    spec.typeVariablesSeq :+ selfPlaceholder

  override protected def contextPremises: Seq[Expr[Prop]] =
    Seq(typingPremise)

  protected val checkReturnType: Map[Pattern[N], JUSTIFICATION] =
    WitnessBase.returnTypeChecks(
      patterns = spec.cases,
      returnType = spec.returnType,
      bodyAt = _.body,
      extraPremisesAt = _ => Set(typingPremise)
    )
}
