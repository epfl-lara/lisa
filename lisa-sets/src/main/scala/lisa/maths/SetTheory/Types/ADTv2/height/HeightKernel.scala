package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UnionRangeCollapse.unionRangeCollapse

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*

object HeightKernel {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  val isConstructor = variable[Ind >>: Ind >>: Prop]

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

  // ––––––––––––––––––––––––––––––––––––––––––––––––

  val introductionFunctionMononotic = Lemma(
    (isConstructorMono, subset(s, t)) |- inIntroImage(s)(x) ==> inIntroImage(t)(x)
  ) {
    val constMono = have(isConstructorMono |- isConstructorMono) by Hypothesis
    have(isConstructorMono |- forall(t, forall(x, subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t))))) by
      InstantiateForall(s)(constMono)
    thenHave(isConstructorMono |- forall(x, subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t)))) by
      InstantiateForall(t)
    thenHave(isConstructorMono |- subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t))) by
      InstantiateForall(x)
    have((isConstructorMono, subset(s, t)) |- isConstructor(x)(s) ==> isConstructor(x)(t)) by
      Tautology.from(lastStep)
    have(thesis) by Cut(lastStep, unionPreimageMonotonic of (P := lam(s, isConstructor(x)(s))))
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

  val heightZero = Lemma(isHeightCore(h) |- !in(x, app(h, ∅))) {
    have(
      isHeightCore(h) |-
        in(x, app(h, ∅)) <=>
        inExtIntroImage(h ↾ ∅)(x)
    ) by Cut(zeroIsNat, heightApplication of (n := ∅))
    thenHave(
      (h ↾ ∅ === ∅, isHeightCore(h)) |- !in(x, app(h, ∅))
    ) by RightSubstEq.withParameters(
      List((h ↾ ∅, ∅)),
      (Seq(s), in(x, app(h, ∅)) <=> inExtIntroImage(s)(x))
    )
    have(thesis) by Cut(restrictedFunctionEmptyDomain, lastStep)
  }

  val heightSuccessorWeak = Lemma(
    (introFunctionMono, isHeightCore(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> inIntroImage(app(h, n))(x)
  ) {
    val heightResNonEmpty: Expr[Prop] = !(h ↾ successor(n) === ∅)

    val coreTyping = have(
      (isHeightCore(h), in(n, N)) |- function(h) /\ (dom(h) === N)
    ) by Tautology
    val nInNFact = have((isHeightCore(h), in(n, N)) |- in(n, N)) by Hypothesis
    val domEq = have((isHeightCore(h), in(n, N)) |- dom(h) === N) by Tautology.from(coreTyping)
    val nInDomH = have((isHeightCore(h), in(n, N)) |- in(n, dom(h))) by Congruence.from(nInNFact, domEq)
    val nInSucc = have((isHeightCore(h), in(n, N)) |- in(n, successor(n))) by
      Tautology.from(nInSuccN of (n := n))

    val heightResNonEmptyLemma = have((isHeightCore(h), in(n, N)) |- heightResNonEmpty) by
      Tautology.from(
        coreTyping,
        nInDomH,
        nInSucc,
        restrictedFunctionNotEmpty of (x := n, d := successor(n))
      )

    have(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N)) |-
        subset(m, n) ==> subset(app(h, m), app(h, n))
    ) by RightImplies(heightMonotonic)
    thenHave(
      (introFunctionMono, isHeightCore(h), in(n, N)) |-
        in(m, N) ==> (subset(m, n) ==> subset(app(h, m), app(h, n)))
    ) by RightImplies
    val monotonicityForall = thenHave(
      (introFunctionMono, isHeightCore(h), in(n, N)) |-
        forall(m, in(m, N) ==> (subset(m, n) ==> subset(app(h, m), app(h, n))))
    ) by RightForall

    val coreTypingAndN = have(
      (isHeightCore(h), in(n, N)) |- (function(h) /\ (dom(h) === N)) /\ in(n, N)
    ) by RightAnd(coreTyping, nInNFact)

    have(
      (introFunctionMono, isHeightCore(h), in(n, N)) |- (
        function(h) /\
        (dom(h) === N) /\
        in(n, N) /\
        forall(m, in(m, N) ==> (subset(m, n) ==> subset(app(h, m), app(h, n))))
      )
    ) by RightAnd(coreTypingAndN, monotonicityForall)

    val unionRangeRes = have(
      (introFunctionMono, isHeightCore(h), in(n, N)) |-
        unionRange(h ↾ successor(n)) === app(h, n)
    ) by Tautology.from(lastStep, unionRangeCollapse)

    val succIsNatStep = have((isHeightCore(h), in(n, N)) |- in(successor(n), N)) by
      Tautology.from(successorIsNat)

    have(
      (isHeightCore(h), in(n, N)) |-
        in(x, app(h, successor(n))) <=>
        inExtIntroImage(h ↾ successor(n))(x)
    ) by Cut(succIsNatStep, heightApplication of (n := successor(n)))

    thenHave(
      (
        isHeightCore(h),
        in(n, N),
        unionRange(h ↾ successor(n)) === app(h, n)
      ) |-
        in(x, app(h, successor(n))) <=>
        heightResNonEmpty /\ inIntroImage(app(h, n))(x)
    ) by RightSubstEq.withParameters(
      List((unionRange(h ↾ successor(n)), app(h, n))),
      (
        Seq(s),
        in(x, app(h, successor(n))) <=>
          (heightResNonEmpty /\ inIntroImage(s)(x))
      )
    )

    have(
      (introFunctionMono, isHeightCore(h), in(n, N)) |-
        in(x, app(h, successor(n))) <=> heightResNonEmpty /\ inIntroImage(app(h, n))(x)
    ) by Cut(unionRangeRes, lastStep)

    have(
      (introFunctionMono, isHeightCore(h), in(n, N), heightResNonEmpty) |-
        in(x, app(h, successor(n))) <=> inIntroImage(app(h, n))(x)
    ) by Cut(lastStep, equivalenceAnd of (
      p1 := in(x, app(h, successor(n))),
      p2 := heightResNonEmpty,
      p3 := inIntroImage(app(h, n))(x)
    ))

    have(thesis) by Cut(heightResNonEmptyLemma, lastStep)
  }

}
