package lisa.maths.SetTheory.Types.ADT.PatternMatching.proofs

import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.encoding._
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._

private[proofs] trait WitnessProofContext {

  protected val adt: SemanticADT
  protected val argType: Expr[Ind]
  protected val patternMatching: PatternSystem[Expr[Ind]]
  protected val returnType: Expr[Ind]
  protected val typ: Expr[Ind]
  protected val witness: Expr[Ind]
  protected val witnessDef: JUSTIFICATION
  protected val witnessBound: Expr[Ind]
  protected val pairWitness: Variable[Ind]
  protected val caseMembership: Expr[Ind] => Expr[Prop]
  protected val checkReturnType: Map[Clause[Expr[Ind]], JUSTIFICATION]
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

  protected val contextPremise: Expr[Prop] = seqAnd(contextPremises)

  protected def contextualize(formula: Expr[Prop]): Expr[Prop] =
    if contextPremises.isEmpty then formula else simplify(contextPremise ==> formula)

}
