package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.DefinedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs.CaseDefinedWitness
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.CartesianProduct.×
import lisa.maths.SetTheory.Base.Comprehension.|
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
private[recursion] final class Witness[N <: Arity](spec: FunSpec[N]) {

  private val typeVariablesSeq: Seq[Variable[Ind]] = spec.typeVariablesSeq
  private val selfPlaceholder: Variable[Ind] = spec.selfPlaceholder
  private val pairWitness: Variable[Ind] = variable[Ind]

  /** typingPremise = selfPlaceholder :: A→T (the induction hypothesis on the self-reference). */
  val typingPremise: Expr[Prop] = selfPlaceholder :: spec.typ

  private val patterns: Seq[Pattern[N]] = spec.cases

  /**
   * caseMembership(p) ≡ ∨_c ∃x̄. WT(c(x̄)) ∧ p = (c(x̄), body_c[selfPlaceholder]).
   *
   * selfPlaceholder is free — W is parametric in the self-reference.
   */
  private val caseMembership: Expr[Ind] => Expr[Prop] = (p: Expr[Ind]) =>
    spec.patternMatching.caseMembership(p)

  private val witnessClass = new DefinedSymbol(
    name = s"${spec.functionName}/witness",
    parametersSeq = typeVariablesSeq :+ selfPlaceholder,
    body = { pairWitness ∈ (spec.argType × spec.returnType) | caseMembership(pairWitness) }
  )

  /** The witness set W(selfPlaceholder) — has selfPlaceholder free. */
  val witness: Expr[Ind] = witnessClass.term

  private val witnessBound: Expr[Ind] = spec.argType × spec.returnType

  /** Definitional equation for the witness: W(selfPlaceholder) = witnessBody. */
  val witnessDef: JUSTIFICATION = witnessClass.definition

  def apply(g: Expr[Ind]): Expr[Ind] =
    witness.substitute(spec.selfPlaceholder := g)

  private def constructorTagDisequality(
      c1: SemanticConstructor[N],
      c2: SemanticConstructor[N]
  ): THM = {
    require(c1 != c2, "constructorTagDisequality requires two distinct constructors.")
    val minTag = Math.min(c1.underlying.tag, c2.underlying.tag)
    val maxTag = Math.max(c1.underlying.tag, c2.underlying.tag)
    lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.constructorTagDisequality(
      c1.underlying.tagTerm,
      c2.underlying.tagTerm,
      minTag,
      maxTag
    )
  }

  private val constructorTagDisequalities: Map[(SemanticConstructor[N], SemanticConstructor[N]), THM] =
    (for
      c1 <- spec.adt.constructors
      c2 <- spec.adt.constructors
      if c1 != c2
    yield (c1, c2) -> constructorTagDisequality(c1, c2)).toMap

  private val checkReturnType: Map[Pattern[N], JUSTIFICATION] =
    patterns.map(pattern =>
      val bodyWithSelf = pattern.body.substitute(selfPlaceholder := selfPlaceholder)
      val witnessAssumptions = pattern.typingPremises + typingPremise
      pattern -> Lemma(witnessAssumptions |- (bodyWithSelf :: spec.returnType)) {
        have(thesis) by Typecheck.prove
      }
    ).toMap

  private val witnessSemantics = Time.measure("Witness/CaseDefinedWitness")(new CaseDefinedWitness[N](
    adt = spec.adt,
    argType = spec.argType,
    patternMatching = spec.patternMatching,
    returnType = spec.returnType,
    typ = spec.typ,
    witness = witness,
    witnessDef = witnessDef,
    witnessBound = witnessBound,
    pairWitness = pairWitness,
    caseMembership = caseMembership,
    checkReturnType = checkReturnType,
    constructorTagDisequalities = constructorTagDisequalities,
    contextPremises = Seq(typingPremise)
  ))

  /** selfPlaceholder :: A→T ⊢ W(selfPlaceholder) :: A→T */
  val witnessHasType: THM = witnessSemantics.witnessHasType

  /**
   * selfPlaceholder :: A→T ⊢ W(selfPlaceholder)(c(x̄)) = body_c[selfPlaceholder]
   */
  val witnessCaseByPattern: Map[Pattern[N], THM] =
    witnessSemantics.witnessCaseByPattern

  def witnessCase(pattern: Pattern[N]): THM =
    witnessSemantics.witnessCase(pattern)
}
