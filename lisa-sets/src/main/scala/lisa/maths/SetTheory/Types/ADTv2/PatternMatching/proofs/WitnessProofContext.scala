package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs

import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.ConstructorHeadPattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.utils.prooflib.ProofTacticLib.Arity

private[proofs] trait WitnessProofContext[N <: Arity] {

  protected val adt: SemanticADT[N]
  protected val argType: Expr[Ind]
  protected val patternMatching: PatternSystem[N]
  protected val returnType: Expr[Ind]
  protected val typ: Expr[Ind]
  protected val witness: Expr[Ind]
  protected val witnessDef: JUSTIFICATION
  protected val witnessBound: Expr[Ind]
  protected val pairWitness: Variable[Ind]
  protected val caseMembership: Expr[Ind] => Expr[Prop]
  protected val checkReturnType: Map[Pattern[N], JUSTIFICATION]
  protected val contextPremises: Seq[Expr[Prop]]

  protected val inputTerm: Variable[Ind] = variable[Ind]
  protected val outputTerm: Variable[Ind] = variable[Ind]
  protected val alternateOutputTerm: Variable[Ind] = variable[Ind]

  protected val witnessBody: Expr[Ind] = { pairWitness ∈ witnessBound | caseMembership(pairWitness) }

  protected val patternCaseMembership: Expr[Ind] => Expr[Prop] =
    patternMatching.caseMembership

  require(
    caseMembership(pairWitness) == patternCaseMembership(pairWitness),
    "CaseDefinedWitness expects caseMembership to coincide with patternMatching.caseMembership."
  )

  protected val contextPremise: Expr[Prop] =
    simplify(seqAnd(contextPremises))

  protected def contextualize(formula: Expr[Prop]): Expr[Prop] =
    if contextPremises.isEmpty then formula else contextPremise ==> formula

  protected def constructorHead(pattern: Pattern[N]): ConstructorHeadPattern[N] =
    ConstructorHeadPattern.require(pattern)
}
