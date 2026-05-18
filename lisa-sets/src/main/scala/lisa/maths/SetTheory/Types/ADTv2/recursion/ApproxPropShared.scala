package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.recursion.NatFacts.Succ
import lisa.maths.SetTheory.Base.{FoundationAxiom, Subset}
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.ProofTacticLib.Arity

object ApproxPropShared {
  private val nVar = variable[Ind]
  private val kVar = variable[Ind]

  def constructorBranchAtHeight[N <: Arity](
      c: SemanticConstructor[N],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    c.branchAtHeight(heightSet, term)

  def constructorBranchesAtHeight[N <: Arity](
      constructors: Seq[SemanticConstructor[N]],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Map[SemanticConstructor[N], Expr[Prop]] =
    constructors.map(c => c -> constructorBranchAtHeight(c, heightSet, term)).toMap

  def constructorDisjunctionAtHeight[N <: Arity](
      constructors: Seq[SemanticConstructor[N]],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    seqOr(constructors.map(c => constructorBranchAtHeight(c, heightSet, term)))

  def substitutedCaseBody[N <: Arity](
      spec: FunSpec[N],
      c: SemanticConstructor[N],
      selfTerm: Expr[Ind]
  ): Expr[Ind] = {
    val (caseVars, rawBody) = spec.rawCases(c)
    rawBody
      .substitute(spec.selfPlaceholder := selfTerm)
      .substitute(caseVars.zip(c.variables2).map((from, to) => from := to)*)
      .asInstanceOf[Expr[Ind]]
  }

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

  def TAbsConstOn(
      domain: Expr[Ind],
      codomain: Expr[Ind],
      body: Expr[Ind >>: Ind]
  ): THM = Lemma(
    ∀(x ∈ domain, body(x) ∈ codomain) |- abs(domain)(body) ∈ Pi(domain)(λ(y, codomain))
  ) {
    val e = variable[Ind >>: Ind]
    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]

    assume(∀(x ∈ domain, body(x) ∈ codomain))
    val premiseAtX = have(x ∈ domain ==> body(x) ∈ codomain) by InstantiateForall
    have(x ∈ domain ==> body(x) ∈ λ(y, codomain)(x)) by
      Tautology.from(premiseAtX)
    thenHave(∀(x ∈ domain, body(x) ∈ λ(y, codomain)(x))) by RightForall
    have(abs(domain)(body) ∈ Pi(domain)(λ(y, codomain))) by
      Tautology.from(lastStep, TAbs of (T1 := domain, T2 := λ(y, codomain), e := body))
    thenHave(thesis) by Restate
  }
}
