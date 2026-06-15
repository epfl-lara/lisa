package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Functions.BasicTheorems.functionOnDomain
import lisa.maths.SetTheory.Functions.BasicTheorems.functionOnIsFunction
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.natNotEmpty
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.OmegaFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.TransfiniteRecursionExt
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems._

private[height] object CoreFacts {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  val isConstructor = variable[Ind >>: Ind >>: Prop]
  val stageSet = variable[Ind >>: Ind]

  private val unionPreimageMonotonic =
    Lemma((s ⊆ t, P(s) ==> P(t)) |- (P(s) \/ (x ∈ s)) ==> (P(t) \/ (x ∈ t))) {
      have(s ⊆ t |- forall(z, (z ∈ s) ==> (z ∈ t))) by Tautology.from(subsetAxiom of (x := s, y := t))
      thenHave(s ⊆ t |- (x ∈ s) ==> (x ∈ t)) by InstantiateForall(x)
      have(thesis) by Cut(
        lastStep,
        disjunctionsImplies of (p1 := x ∈ s, p2 := x ∈ t, q1 := P(s), q2 := P(t))
      )
    }

  def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    isConstructor(y)(s) \/ in(y, s)

  def inExtIntroImage(f: Expr[Ind])(x: Expr[Ind]): Expr[Prop] =
    (f =/= ∅) /\ inIntroImage(unionRange(f))(x)

  def isHeightCore(h: Expr[Ind]): Expr[Prop] =
    function(h) /\
    (dom(h) === N) /\
    ∀(n ∈ N, ∀(x, in(x, app(h, n)) <=> inExtIntroImage(h ↾ n)(x)))

  val introFunctionMono: Expr[Prop] =
    forall(s, forall(t, subset(s, t) ==> forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))))

  val isConstructorMono: Expr[Prop] =
    forall(s, forall(t, forall(x, subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t)))))

  val stageSetSpec: Expr[Prop] =
    forall(f, forall(x, in(x, stageSet(f)) <=> inExtIntroImage(f)(x)))

  val stageSetExists = Lemma(
    stageSetSpec |- exists(s, forall(x, in(x, s) <=> inExtIntroImage(f)(x)))
  ) {
    assume(stageSetSpec)
    have(stageSetSpec |- stageSetSpec) by Hypothesis
    thenHave(stageSetSpec |- forall(x, in(x, stageSet(f)) <=> inExtIntroImage(f)(x))) by
      InstantiateForall(f)
    thenHave(stageSetSpec |- exists(s, forall(x, in(x, s) <=> inExtIntroImage(f)(x)))) by
      RightExists
    thenHave(thesis) by Restate
  }

  val heightExists = Lemma(stageSetSpec |- exists(h, isHeightCore(h))) {
    val Func = variable[Ind >>: Ind >>: Ind]
    val stepFunc: Expr[Ind >>: Ind >>: Ind] = λ(n, stageSet)
    val recFun = TransfiniteRecursionExt.transfiniteRecursionFunction(stepFunc)(N)

    val recSpec0 = have(
      functionOn(recFun)(N) /\
        ∀(n ∈ N, app(recFun, n) === stepFunc(n)(recFun ↾ n))
    ) by Tautology.from(
      OmegaFacts.isOrdinal,
      TransfiniteRecursionExt.transfiniteRecursionFunctionSpec.of(Func := stepFunc, α := N)
    )
    val recSpec = have(
      stageSetSpec |-
        functionOn(recFun)(N) /\
          ∀(n ∈ N, app(recFun, n) === stepFunc(n)(recFun ↾ n))
    ) by Weakening(recSpec0)

    val funOnRec = have(stageSetSpec |- functionOn(recFun)(N)) by Tautology.from(recSpec)
    val recIsFun = have(stageSetSpec |- function(recFun)) by Tautology.from(
      funOnRec,
      functionOnIsFunction of (f := recFun, A := N)
    )
    val recDom = have(stageSetSpec |- dom(recFun) === N) by Tautology.from(
      funOnRec,
      functionOnDomain of (f := recFun, A := N)
    )

    val stageEqAll = have(
      stageSetSpec |-
        ∀(n ∈ N, app(recFun, n) === stepFunc(n)(recFun ↾ n))
    ) by Tautology.from(recSpec)

    val stageChar = have(
      (stageSetSpec, in(n, N)) |-
        ∀(x, in(x, app(recFun, n)) <=> inExtIntroImage(recFun ↾ n)(x))
    ) subproof {
      val recEq0 = have(
        (stageSetSpec, in(n, N)) |-
          app(recFun, n) === stepFunc(n)(recFun ↾ n)
      ) by InstantiateForall(n)(stageEqAll)
      val stepEq = have(
        stepFunc(n)(recFun ↾ n) === stageSet(recFun ↾ n)
      ) by Restate
      val recEq = have(
        (stageSetSpec, in(n, N)) |-
          app(recFun, n) === stageSet(recFun ↾ n)
      ) by Congruence.from(recEq0, stepEq)

      val stageSetSpecFact = have(stageSetSpec |- stageSetSpec) by Hypothesis
      val stageSpecAtRec = have(
        stageSetSpec |-
          ∀(x, in(x, stageSet(recFun ↾ n)) <=> inExtIntroImage(recFun ↾ n)(x))
      ) by InstantiateForall(recFun ↾ n)(stageSetSpecFact)

      val stageMemEq = have(
        stageSetSpec |-
          in(x, stageSet(recFun ↾ n)) <=> inExtIntroImage(recFun ↾ n)(x)
      ) by InstantiateForall(x)(stageSpecAtRec)

      have(
        (stageSetSpec, in(n, N)) |-
          in(x, app(recFun, n)) <=> inExtIntroImage(recFun ↾ n)(x)
      ) by Congruence.from(recEq, stageMemEq)
      thenHave(
        (stageSetSpec, in(n, N)) |-
          ∀(x, in(x, app(recFun, n)) <=> inExtIntroImage(recFun ↾ n)(x))
      ) by RightForall
    }

    val stageAll = have(
      stageSetSpec |-
        ∀(n ∈ N, ∀(x, in(x, app(recFun, n)) <=> inExtIntroImage(recFun ↾ n)(x)))
    ) subproof {
      have(
        (stageSetSpec, in(n, N)) |-
          ∀(x, in(x, app(recFun, n)) <=> inExtIntroImage(recFun ↾ n)(x))
      ) by Restate.from(stageChar)
      thenHave(
        stageSetSpec |- in(n, N) ==> ∀(x, in(x, app(recFun, n)) <=> inExtIntroImage(recFun ↾ n)(x))
      ) by RightImplies
      thenHave(
        stageSetSpec |-
          ∀(n, in(n, N) ==> ∀(x, in(x, app(recFun, n)) <=> inExtIntroImage(recFun ↾ n)(x)))
      ) by RightForall
      thenHave(thesis) by Restate
    }

    have(stageSetSpec |- isHeightCore(recFun)) by Tautology.from(recIsFun, recDom, stageAll)
    thenHave(stageSetSpec |- exists(h, isHeightCore(h))) by RightExists
    thenHave(thesis) by Restate
  }

  val isConstructorMonotonic = Lemma(
    (isConstructorMono, subset(s, t)) |- isConstructor(x)(s) ==> isConstructor(x)(t)
  ) {
    val constMono = have(isConstructorMono |- isConstructorMono) by Hypothesis
    have(isConstructorMono |- forall(t, forall(x, subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t))))) by
      InstantiateForall(s)(constMono)
    thenHave(isConstructorMono |- forall(x, subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t)))) by
      InstantiateForall(t)
    thenHave(isConstructorMono |- subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t))) by
      InstantiateForall(x)
    have(thesis) by Tautology.from(lastStep)
  }

  val introductionFunctionMononotic = Lemma(
    (isConstructorMono, subset(s, t)) |- inIntroImage(s)(x) ==> inIntroImage(t)(x)
  ) {
    have(thesis) by Cut(
      isConstructorMonotonic,
      unionPreimageMonotonic of (P := lam(s, isConstructor(x)(s)))
    )
  }

  val domNImpliesNonEmpty = Lemma(dom(h) === N |- !(h === ∅)) {
    have(dom(h) === N |- !(dom(h) === ∅)) by Congruence.from(natNotEmpty)
    have(dom(h) === N |- !(h === ∅)) by Tautology.from(lastStep, nonEmptyDomain)
  }

  val extIntroMonotonic = Lemma(
    (introFunctionMono, subset(f, g)) |-
      inExtIntroImage(f)(x) ==>
      inExtIntroImage(g)(x)
  ) {
    val introUnionF = inIntroImage(unionRange(f))(x)
    val introUnionG = inIntroImage(unionRange(g))(x)

    val introMono = have(introFunctionMono |- introFunctionMono) by Hypothesis
    have(
      introFunctionMono |-
        subset(unionRange(f), unionRange(g)) ==>
        forall(x, introUnionF ==> introUnionG)
    ) by InstantiateForall(unionRange(f), unionRange(g))(introMono)
    have((introFunctionMono, subset(f, g)) |- forall(x, introUnionF ==> introUnionG)) by
      Tautology.from(lastStep, unionRangeMonotonic)
    thenHave((introFunctionMono, subset(f, g)) |- introUnionF ==> introUnionG) by
      InstantiateForall(x)
    val left = thenHave((introFunctionMono, subset(f, g), introUnionF) |- introUnionG) by Restate

    have(
      (introFunctionMono, subset(f, g), !(f === ∅), introUnionF) |-
        inExtIntroImage(g)(x)
    ) by RightAnd(left, subsetNotEmpty of (x := f, y := g))
  }

  val heightApplication = Lemma(
    (isHeightCore(h), in(n, N)) |-
      in(x, app(h, n)) <=>
      inExtIntroImage(h ↾ n)(x)
  ) {
    val extIntroResM = inExtIntroImage(h ↾ n)(x)
    val heightFunApplicationDef = forall(
      n,
      in(n, N) ==> forall(x, in(x, app(h, n)) <=> extIntroResM)
    )

    have(isHeightCore(h) |- heightFunApplicationDef) by Tautology
    thenHave((isHeightCore(h), in(n, N)) |- heightFunApplicationDef) by Weakening
    thenHave(
      (isHeightCore(h), in(n, N)) |-
        in(n, N) ==> forall(x, in(x, app(h, n)) <=> extIntroResM)
    ) by InstantiateForall(n)
    thenHave(
      (isHeightCore(h), in(n, N)) |-
        forall(x, in(x, app(h, n)) <=> extIntroResM)
    ) by Restate
    thenHave(
      (isHeightCore(h), in(n, N)) |-
        in(x, app(h, n)) <=> extIntroResM
    ) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }

  val heightMonotonic = Lemma(
    (introFunctionMono, isHeightCore(h), in(n, N), in(m, N), subset(m, n)) |-
      subset(app(h, m), app(h, n))
  ) {
    val extIntroResM = inExtIntroImage(h ↾ m)(x)
    val extIntroResN = inExtIntroImage(h ↾ n)(x)

    have(
      (isHeightCore(h), n ∈ N, m ∈ N, m ⊆ n) |- (x ∈ app(h, m)) <=> extIntroResM
    ) by Tautology.from(heightApplication of (n := m))

    val unfoldHeightApplicationM = have(
      (isHeightCore(h), in(n, N), in(m, N), subset(m, n), in(x, app(h, m))) |-
        extIntroResM
    ) by Cut(
      lastStep,
      equivalenceRevApply of (p1 := in(x, app(h, m)), p2 := extIntroResM)
    )

    have(
      (introFunctionMono, subset(m, n)) |-
        extIntroResM ==>
        extIntroResN
    ) by Cut(
      restrictedFunctionDomainMonotonic of (x := m, y := n, f := h),
      extIntroMonotonic of (f := h ↾ m, g := h ↾ n)
    )
    val extNFromMonotonic = have(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N), subset(m, n), extIntroResM) |-
        extIntroResN
    ) by Tautology.from(lastStep)

    val inHnFromExtended = have(
      (isHeightCore(h), in(n, N), extIntroResN) |-
        in(x, app(h, n))
    ) by Cut(
      heightApplication of (n := n),
      equivalenceRevApply of (p1 := extIntroResN, p2 := in(x, app(h, n)))
    )

    have(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N), subset(m, n), extIntroResM) |-
        in(x, app(h, n))
    ) by Cut(extNFromMonotonic, inHnFromExtended)

    have(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N), subset(m, n), in(x, app(h, m))) |-
        in(x, app(h, n))
    ) by Cut(unfoldHeightApplicationM, lastStep)
    thenHave(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N), subset(m, n)) |-
        in(x, app(h, m)) ==> in(x, app(h, n))
    ) by RightImplies
    thenHave(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N), subset(m, n)) |-
        forall(x, in(x, app(h, m)) ==> in(x, app(h, n)))
    ) by RightForall

    have(thesis) by Tautology.from(
      subsetAxiom of (x := app(h, m), y := app(h, n)),
      equivalenceRevApply of (
        p1 := forall(x, in(x, app(h, m)) ==> in(x, app(h, n))),
        p2 := subset(app(h, m), app(h, n))
      ),
      lastStep
    )
  }

  def stageSetExistsAt(
      stageSet0: Expr[Ind >>: Ind],
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      f0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    stageSetExists.of(stageSet := stageSet0, isConstructor := isConstructor0, f := f0)

  def heightExistsAt(
      stageSet0: Expr[Ind >>: Ind],
      isConstructor0: Expr[Ind >>: Ind >>: Prop]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightExists.of(stageSet := stageSet0, isConstructor := isConstructor0)

  def isConstructorMonotonicAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      s0: Expr[Ind],
      t0: Expr[Ind],
      x0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    isConstructorMonotonic.of(isConstructor := isConstructor0, s := s0, t := t0, x := x0)

  def introductionFunctionMononoticAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      s0: Expr[Ind],
      t0: Expr[Ind],
      x0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    introductionFunctionMononotic.of(isConstructor := isConstructor0, s := s0, t := t0, x := x0)

  def domNImpliesNonEmptyAt(h0: Expr[Ind])(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    domNImpliesNonEmpty.of(h := h0)

  def extIntroMonotonicAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      f0: Expr[Ind],
      g0: Expr[Ind],
      x0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    extIntroMonotonic.of(isConstructor := isConstructor0, f := f0, g := g0, x := x0)

  def heightApplicationAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      h0: Expr[Ind],
      n0: Expr[Ind],
      x0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightApplication.of(isConstructor := isConstructor0, h := h0, n := n0, x := x0)

  def heightMonotonicAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      h0: Expr[Ind],
      n0: Expr[Ind],
      m0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightMonotonic.of(isConstructor := isConstructor0, h := h0, n := n0, m := m0)

  def initialize(): Unit = {
    val _ = stageSetExists
    val _ = heightExists
    val _ = isConstructorMonotonic
    val _ = introductionFunctionMononotic
    val _ = domNImpliesNonEmpty
    val _ = extIntroMonotonic
    val _ = heightApplication
    val _ = heightMonotonic
  }
}
