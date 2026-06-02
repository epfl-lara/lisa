package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{TypeSubstitution, instantiatedSemanticSignature, specializeFormula, specializeTerm}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.FunctionAbstractions.TAbsConstOn
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Succ
import lisa.maths.SetTheory.Base.{FoundationAxiom, Subset}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts

object ApproxPropShared {
  private val nVar = variable[Ind]
  private val kVar = variable[Ind]

  final case class SpecializedSemanticConstructor[N <: Arity](
      underlying: SemanticConstructor[N],
      typeSubstitutions: Seq[TypeSubstitution]
  ) {
    def name: String = underlying.name
    def variables2: Seq[Variable[Ind]] = underlying.variables2
    def selfRefVariables2: Seq[Variable[Ind]] = underlying.selfRefVariables2
    def semanticSignature2: Seq[(Variable[Ind], Expr[Ind])] =
      instantiatedSemanticSignature(underlying.semanticSignature2, typeSubstitutions)
    def heightTypingFormula(heightSet: Expr[Ind]): Expr[Prop] =
      specializeFormula(underlying.heightTypingFormula(heightSet), typeSubstitutions)
    def branchPremiseAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      specializeFormula(underlying.branchPremiseAtHeight(heightSet, term), typeSubstitutions)
    def branchAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      specializeFormula(underlying.branchAtHeight(heightSet, term), typeSubstitutions)
    def appliedTerm2: Expr[Ind] =
      specializeTerm(underlying.appliedTerm2, typeSubstitutions)
    def semanticTypingFromHeight(heightFun: Expr[Ind], n: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM =
      underlying.semanticTypingFromHeightAt(typeSubstitutions)(heightFun, n)
    def appliedEqualityFromStructural(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM =
      underlying.appliedEqualityFromStructuralAt(typeSubstitutions)(heightFun, n, term0)
  }

  def specializedConstructors[N <: Arity](
      constructors: Seq[SemanticConstructor[N]],
      typeSubstitutions: Seq[TypeSubstitution]
  ): Seq[SpecializedSemanticConstructor[N]] =
    constructors.map(SpecializedSemanticConstructor(_, typeSubstitutions))

  def TAbsConstOn(
      domain: Expr[Ind],
      codomain: Expr[Ind],
      body: Expr[Ind >>: Ind]
  ): THM = lisa.maths.SetTheory.Types.ADTv2.support.proofs.FunctionAbstractions.TAbsConstOn(
    domain,
    codomain,
    body
  )

  def constructorBranchAtHeight[N <: Arity](
      c: SpecializedSemanticConstructor[N],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    c.branchAtHeight(heightSet, term)

  def constructorBranchesAtHeight[N <: Arity](
      constructors: Seq[SpecializedSemanticConstructor[N]],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Map[SpecializedSemanticConstructor[N], Expr[Prop]] =
    constructors.map(c => c -> constructorBranchAtHeight(c, heightSet, term)).toMap

  def constructorDisjunctionAtHeight[N <: Arity](
      constructors: Seq[SpecializedSemanticConstructor[N]],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    seqOr(constructors.map(c => constructorBranchAtHeight(c, heightSet, term)))

  def substitutedCaseBody[N <: Arity](
      spec: FunSpec[N],
      c: SemanticConstructor[N],
      selfTerm: Expr[Ind]
  ): Expr[Ind] = {
    val pattern = spec.patternMatching.patternFor(c)
    pattern.body
      .substitute(spec.selfPlaceholder := selfTerm)
      .substitute(pattern.binders.zip(c.variables2).map((from, to) => from := to)*)
      .asInstanceOf[Expr[Ind]]
  }

  def substitutedCaseBody[N <: Arity](
      pattern: Pattern[N],
      selfPlaceholder: Variable[Ind],
      selfTerm: Expr[Ind],
      vars: Seq[Variable[Ind]]
  ): Expr[Ind] =
    pattern.body
      .substitute(selfPlaceholder := selfTerm)
      .substitute(pattern.binders.zip(vars).map((from, to) => from := to)*)
      .asInstanceOf[Expr[Ind]]

  lazy val subsetBelowSuccN: THM = Lemma(
    (nVar ∈ N, kVar ∈ N, nVar ⊆ Succ(kVar)) |- (nVar === Succ(kVar)) \/ (nVar ⊆ kVar)
  ) {
    val nInN = assume(nVar ∈ N)
    val kInN = assume(kVar ∈ N)
    val nSubSk = assume(nVar ⊆ Succ(kVar))

    val SkInN = have(Succ(kVar) ∈ N) by
      Tautology.from(kInN, NatFacts.succIntro.of(n := kVar))

    val cmp = have(
      (nVar === Succ(kVar)) \/ (nVar ∈ Succ(kVar)) \/ (Succ(kVar) ∈ nVar)
    ) by Tautology.from(
      nInN,
      SkInN,
      NatFacts.comparability of (m := nVar, n := Succ(kVar))
    )

    val caseEq = have(
      nVar === Succ(kVar) |- (nVar === Succ(kVar)) \/ (nVar ⊆ kVar)
    ) by Tautology

    val caseIn = have(
      nVar ∈ Succ(kVar) |- (nVar === Succ(kVar)) \/ (nVar ⊆ kVar)
    ) subproof {
      val nInSk = assume(nVar ∈ Succ(kVar))
      val split = have((nVar ∈ kVar) \/ (nVar === kVar)) by Tautology.from(
        nInSk,
        NatFacts.succMembership.of(k := nVar, n := kVar)
      )

      val fromIn = have(nVar ∈ kVar |- nVar ⊆ kVar) subproof {
        val nInK = assume(nVar ∈ kVar)
        val kTrans = have(TransitiveSet.transitiveSet(kVar)) by
          Tautology.from(kInN, NatFacts.elementsTransitive.of(n := kVar))
        have(nVar ⊆ kVar) by Tautology.from(
          nInK,
          kTrans,
          TransitiveSet.elementIsSubset.of(A := kVar, x := nVar)
        )
      }

      val fromEq = have(nVar === kVar |- nVar ⊆ kVar) by
        Congruence.from(Subset.reflexivity of (x := kVar))

      have(nVar ⊆ kVar) by Tautology.from(split, fromIn, fromEq)
      thenHave(thesis) by Tautology
    }

    val caseGt = have(
      Succ(kVar) ∈ nVar |- (nVar === Succ(kVar)) \/ (nVar ⊆ kVar)
    ) subproof {
      val SkInN = assume(Succ(kVar) ∈ nVar)
      val SkInSk = have(Succ(kVar) ∈ Succ(kVar)) by Tautology.from(
        nSubSk,
        SkInN,
        Subset.membership of (x := nVar, y := Succ(kVar), z := Succ(kVar))
      )
      have(thesis) by Tautology.from(
        SkInSk,
        FoundationAxiom.selfNonInclusion of (x := Succ(kVar))
      )
    }

    have(thesis) by Tautology.from(cmp, caseEq, caseIn, caseGt)
  }
}
