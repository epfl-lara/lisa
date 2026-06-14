package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.Base.CartesianProduct.×
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs.CaseDefinedWitness
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.DefinedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

private[ADTv2] abstract class WitnessBase[N <: Arity](
    functionName: String,
    adt: SemanticADT[N],
    argType: Expr[Ind],
    patternMatching: PatternSystem[N],
    returnType: Expr[Ind],
    typ: Expr[Ind],
    typeVariablesSeq: Seq[Variable[Ind]]
) {

  private val pairWitness: Variable[Ind] = variable[Ind]

  protected def witnessParametersSeq: Seq[Variable[Ind]] = typeVariablesSeq
  protected def contextPremises: Seq[Expr[Prop]] = Seq.empty
  protected def checkReturnType: Map[Pattern[N], JUSTIFICATION]

  private val caseMembership: Expr[Ind] => Expr[Prop] =
    (p: Expr[Ind]) => patternMatching.caseMembership(p)

  private lazy val witnessClass = new DefinedSymbol(
    name = s"${functionName}/witness",
    parametersSeq = witnessParametersSeq,
    body = { pairWitness ∈ (argType × returnType) | caseMembership(pairWitness) }
  )

  lazy val witness: Expr[Ind] = witnessClass.term

  protected lazy val witnessDefCore: JUSTIFICATION = witnessClass.definition

  private val witnessBound: Expr[Ind] = argType × returnType

  private def constructorTagDisequality(
      c1: SemanticConstructor[N],
      c2: SemanticConstructor[N]
  ): THM = {
    require(c1 != c2, "constructorTagDisequality requires two distinct constructors.")
    val minTag = Math.min(c1.underlying.tag, c2.underlying.tag)
    val maxTag = Math.max(c1.underlying.tag, c2.underlying.tag)
    UsefulTheorems.constructorTagDisequality(
      c1.underlying.tagTerm,
      c2.underlying.tagTerm,
      minTag,
      maxTag
    )
  }

  private lazy val constructorTagDisequalities: Map[(SemanticConstructor[N], SemanticConstructor[N]), THM] =
    (for
      c1 <- adt.constructors
      c2 <- adt.constructors
      if c1 != c2
    yield (c1, c2) -> constructorTagDisequality(c1, c2)).toMap

  protected lazy val witnessSemantics: CaseDefinedWitness[N] =
    Time.measure("Witness/CaseDefinedWitness")(new CaseDefinedWitness[N](
      adt = adt,
      argType = argType,
      patternMatching = patternMatching,
      returnType = returnType,
      typ = typ,
      witness = witness,
      witnessDef = witnessDefCore,
      witnessBound = witnessBound,
      pairWitness = pairWitness,
      caseMembership = caseMembership,
      checkReturnType = checkReturnType,
      constructorTagDisequalities = constructorTagDisequalities,
      contextPremises = contextPremises
    ))

  lazy val witnessHasType: THM = witnessSemantics.witnessHasType

  lazy val witnessCaseByPattern: Map[Pattern[N], THM] =
    witnessSemantics.witnessCaseByPattern

  def witnessCase(pattern: Pattern[N]): THM =
    witnessSemantics.witnessCase(pattern)
}

object WitnessBase {

  /**
   * For each pattern, the branch return-type check `body :: returnType` under
   * the pattern's typing premises (plus any extra contextual premises, e.g. the
   * recursive induction hypothesis). Supplied to [[WitnessBase.checkReturnType]].
   */
  def returnTypeChecks[N <: Arity](
      patterns: Seq[Pattern[N]],
      returnType: Expr[Ind],
      bodyAt: Pattern[N] => Expr[Ind],
      extraPremisesAt: Pattern[N] => Set[Expr[Prop]] = (_: Pattern[N]) => Set.empty
  ): Map[Pattern[N], JUSTIFICATION] =
    patterns.map(pattern =>
      pattern -> Lemma((pattern.typingPremises ++ extraPremisesAt(pattern)) |- (bodyAt(pattern) :: returnType)) {
        have(thesis) by Typecheck.prove
      }
    ).toMap
}
