package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Functions.BasicTheorems.functionOnDomain
import lisa.maths.SetTheory.Functions.BasicTheorems.functionOnIsFunction
import lisa.maths.SetTheory.Functions.Operations.Restriction.setMonotonic
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Functions.UnionRange.unionRangeMonotonic
import lisa.maths.SetTheory.Base.Subset.supersetNotEmpty
import lisa.maths.SetTheory.Ordinals.TransfiniteRecursion
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinal
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Ordinals.OmegaFacts

private[height] object CoreFacts {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  val isConstructor = variable[Ind >>: Ind >>: Prop]
  val stageSet = variable[Ind >>: Ind]

  def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    isConstructor(y)(s) \/ (y ∈ s)

  def inExtIntroImage(f: Expr[Ind])(x: Expr[Ind]): Expr[Prop] =
    (f =/= ∅) /\ inIntroImage(⋃(range(f)))(x)

  def isHeightCore(h: Expr[Ind]): Expr[Prop] =
    function(h) /\
      (dom(h) === N) /\
      ∀(n ∈ N, ∀(x, x ∈ app(h, n) <=> inExtIntroImage(h ↾ n)(x)))

  val introFunctionMono: Expr[Prop] =
    ∀(s, ∀(t, s ⊆ t ==> ∀(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))))

  val isConstructorMono: Expr[Prop] =
    ∀(s, ∀(t, ∀(x, s ⊆ t ==> (isConstructor(x)(s) ==> isConstructor(x)(t)))))

  val stageSetSpec: Expr[Prop] =
    ∀(f, ∀(x, x ∈ stageSet(f) <=> inExtIntroImage(f)(x)))

  private val heightExists = Lemma(stageSetSpec |- exists(h, isHeightCore(h))) {
    val Func = variable[Ind >>: Ind >>: Ind]
    val stepFunc: Expr[Ind >>: Ind >>: Ind] = λ(n, stageSet)
    val recFun = TransfiniteRecursion.transfiniteRecursionFunction(stepFunc)(N)
    assume(stageSetSpec)


    val recSpec0 = have(
      ordinal(N) |-
        functionOn(recFun)(N) /\
        ∀(n ∈ N, app(recFun, n) === stepFunc(n)(recFun ↾ n))
    ) by Tautology.from(
      TransfiniteRecursion.transfiniteRecursionFunctionSpec.of(Func := stepFunc, α := N)
    )
    val recSpec = have(
      functionOn(recFun)(N) /\ ∀(n ∈ N, app(recFun,n) === stepFunc(n)(recFun ↾ n))
    ) by Cut(OmegaFacts.isOrdinal, recSpec0)

    have(
      ∀(n ∈ N, app(recFun, n) === stepFunc(n)(recFun ↾ n))
    ) by Weakening(recSpec)
    val recEq0 = thenHave(
      n ∈ N |- app(recFun, n) === stepFunc(n)(recFun ↾ n)
    ) by InstantiateForall(n)

    val stepEq = have(
      stepFunc(n)(recFun ↾ n) === stageSet(recFun ↾ n)
    ) by Restate

    val stageSetSpecFact = have(stageSetSpec) by Hypothesis
    val stageSpecAtRec = have(
      ∀(x, x ∈ stageSet(recFun ↾ n) <=> inExtIntroImage(recFun ↾ n)(x))
    ) by InstantiateForall(recFun ↾ n)(stageSetSpecFact)

    val stageMemEq = have(
      x ∈ stageSet(recFun ↾ n) <=> inExtIntroImage(recFun ↾ n)(x)
    ) by InstantiateForall(x)(stageSpecAtRec)

    have(
      n ∈ N |- x ∈ app(recFun, n) <=> inExtIntroImage(recFun ↾ n)(x)
    ) by Congruence.from(recEq0, stepEq, stageMemEq)
    val stageChar = thenHave(
      n ∈ N |-
        ∀(x, x ∈ app(recFun, n) <=> inExtIntroImage(recFun ↾ n)(x))
    ) by RightForall

    have(
      n ∈ N ==> ∀(x, x ∈ app(recFun, n) <=> inExtIntroImage(recFun ↾ n)(x))
    ) by RightImplies(stageChar)
    val stageAll = thenHave(
      ∀(n ∈ N, ∀(x, x ∈ app(recFun, n) <=> inExtIntroImage(recFun ↾ n)(x)))
    ) by RightForall

    val isFunOn = have(functionOn(recFun)(N)) by Weakening(recSpec)
    val isFun = have(function(recFun)) by Cut(isFunOn, functionOnIsFunction of (f := recFun, A := N))
    val isDomN = have(dom(recFun) === N) by Cut(isFunOn, functionOnDomain of (f := recFun, A := N))

    have(isHeightCore(recFun)) by RightAnd(
      isFun,
      isDomN,
      stageAll
    )


    thenHave(∃(h, isHeightCore(h))) by RightExists
    thenHave(thesis) by Restate
  }

  val isConstructorMonotonic = Lemma(
    (isConstructorMono, s ⊆ t) |- isConstructor(x)(s) ==> isConstructor(x)(t)
  ) {
    have(isConstructorMono |- isConstructorMono) by Hypothesis
    thenHave(isConstructorMono |- ∀(t, ∀(x, s ⊆ t ==> (isConstructor(x)(s) ==> isConstructor(x)(t))))) by
      InstantiateForall(s)
    thenHave(isConstructorMono |- ∀(x, s ⊆ t ==> (isConstructor(x)(s) ==> isConstructor(x)(t)))) by
      InstantiateForall(t)
    thenHave(isConstructorMono |- s ⊆ t ==> (isConstructor(x)(s) ==> isConstructor(x)(t))) by
      InstantiateForall(x)
    thenHave(thesis) by Restate
  }

  private val extIntroMonotonic = Lemma(
    (introFunctionMono, f ⊆ g) |-
      inExtIntroImage(f)(x) ==>
      inExtIntroImage(g)(x)
  ) {
    val introUnionF = inIntroImage(⋃(range(f)))(x)
    val introUnionG = inIntroImage(⋃(range(g)))(x)
    assume(introFunctionMono, f ⊆ g)

    val introMono = have(introFunctionMono) by Hypothesis
    have((⋃(range(f)) ⊆ ⋃(range(g))) ==> ∀(x, introUnionF ==> introUnionG)
    ) by InstantiateForall(⋃(range(f)), ⋃(range(g)))(introMono)
    thenHave((⋃(range(f)) ⊆ ⋃(range(g))) |- ∀(x, introUnionF ==> introUnionG)) by Restate
    have(f ⊆ g |- ∀(x, introUnionF ==> introUnionG)) by
      Cut(unionRangeMonotonic, lastStep)
    thenHave(introUnionF ==> introUnionG) by
      InstantiateForall(x)
    val left = thenHave((introFunctionMono, f ⊆ g, introUnionF) |- introUnionG) by Restate

    have(
      (f =/= ∅, introUnionF) |- inExtIntroImage(g)(x)
    ) by RightAnd(left, supersetNotEmpty of (x := f, y := g))
  }

  val heightApplication = Lemma(
    (isHeightCore(h), n ∈ N) |- (x ∈ app(h, n)) <=> inExtIntroImage(h ↾ n)(x)
  ) {
    val extIntroResM = inExtIntroImage(h ↾ n)(x)
    val heightFunApplicationDef = ∀(n ∈ N, ∀(x, (x ∈ app(h, n)) <=> extIntroResM))

    val hyp = assume(isHeightCore(h), n ∈ N)

    have(heightFunApplicationDef) by Weakening(hyp)
    thenHave(
      n ∈ N ==> ∀(x, (x ∈ app(h, n)) <=> extIntroResM)
    ) by InstantiateForall(n)
    thenHave(
      ∀(x, (x ∈ app(h, n)) <=> extIntroResM)
    ) by Restate
    thenHave(
      (x ∈ app(h, n)) <=> extIntroResM
    ) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }

  private[proofs] val heightMonotonic = Lemma(
    (introFunctionMono, isHeightCore(h), n ∈ N, m ∈ N, m ⊆ n) |-
      app(h, m) ⊆ app(h, n)
  ) {
    assume(introFunctionMono, isHeightCore(h), n ∈ N, m ∈ N, m ⊆ n)
    val extIntroResM = inExtIntroImage(h ↾ m)(x)
    val extIntroResN = inExtIntroImage(h ↾ n)(x)

    have(extIntroResM ==> extIntroResN) by Cut(
      setMonotonic of (x := m, y := n, f := h),
      extIntroMonotonic of (f := h ↾ m, g := h ↾ n)
    )
    have((x ∈ app(h, m)) ==> (x ∈ app(h, n))) by 
      Substitute(heightApplication of (n := m), heightApplication)(lastStep)
    thenHave(∀(x, (x ∈ app(h, m)) ==> (x ∈ app(h, n)))) by RightForall
    
    have(thesis) by Congruence.from(
      lastStep,
      subsetAxiom of (x := app(h, m), y := app(h, n))
    )
  }

  def heightExistsAt(
      stageSet0: Expr[Ind >>: Ind],
      isConstructor0: Expr[Ind >>: Ind >>: Prop]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightExists.of(stageSet := stageSet0, isConstructor := isConstructor0)

  def heightMonotonicAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      h0: Expr[Ind],
      n0: Expr[Ind],
      m0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightMonotonic.of(isConstructor := isConstructor0, h := h0, n := n0, m := m0)

  def initialize(): Unit = {
    val _ = heightExists
    val _ = isConstructorMonotonic
    val _ = extIntroMonotonic
    val _ = heightApplication
    val _ = heightMonotonic
  }
}
