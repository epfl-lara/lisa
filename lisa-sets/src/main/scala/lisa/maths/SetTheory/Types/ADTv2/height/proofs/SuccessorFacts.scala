package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Functions.Operations.Restriction.emptyRestriction
import lisa.maths.SetTheory.Functions.Operations.Restriction.notEmpty
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.emptyInOmega
import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Integer.selfInSuccessor
import lisa.maths.SetTheory.Ordinals.Integer.subsetSuccessor
import lisa.maths.SetTheory.Ordinals.Integer.successorInOmega
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.CoreFacts._
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.UnionRangeCollapse.unionRangeCollapse
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts

private[height] object SuccessorFacts {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  val heightZero = Lemma(isHeightCore(h) |- !(x ∈ app(h, ∅))) {
    have(
      isHeightCore(h) |-
        x ∈ app(h, ∅) <=>
        inExtIntroImage(h ↾ ∅)(x)
    ) by Tautology.from(emptyInOmega, CoreFacts.heightApplication.of(n := ∅))
    thenHave(
      (h ↾ ∅ === ∅, isHeightCore(h)) |- !(x ∈ app(h, ∅))
    ) by RightSubst(
      List((h ↾ ∅, ∅)),
      (Seq(s), x ∈ app(h, ∅) <=> inExtIntroImage(s)(x))
    )
    have(thesis) by Cut(emptyRestriction of (f := h), lastStep)
  }

  val heightSuccessorWeak = Lemma(
    (introFunctionMono, isHeightCore(h), n ∈ N) |-
      x ∈ app(h, S(n)) <=> inIntroImage(app(h, n))(x)
  ) {
    val heightResNonEmpty: Expr[Prop] = !(h ↾ S(n) === ∅)

    assume(introFunctionMono, isHeightCore(h), n ∈ N)

    val nInNFact = have(n ∈ N) by Hypothesis
    val domEq = have(dom(h) === N) by Restate
    val nInDomH = have(n ∈ dom(h)) by Congruence.from(nInNFact, domEq)

    val hIsFunc = have(function(h)) by Restate

    have(heightResNonEmpty) by
      Cuts(notEmpty of (f := h, x := n, d := S(n)))(hIsFunc, nInDomH, selfInSuccessor)
    val heightResNonEmptyLemma = have(heightResNonEmpty <=> ⊤) by
      Restate.from(lastStep)

    have(m ∈ N ==> (m ⊆ n ==> app(h, m) ⊆ app(h, n))) by
      Restate.from(CoreFacts.heightMonotonic)
    val monotonicityForall = thenHave(
      ∀(m ∈ N, (m ⊆ n ==> app(h, m) ⊆ app(h, n)))
    ) by RightForall
    val unionRangeRes = have(
      ⋃(range(h ↾ S(n))) === app(h, n)
    ) by Cuts(unionRangeCollapse)(
      hIsFunc,
      domEq,
      monotonicityForall
    )

    val succIsNatStep = have(S(n) ∈ N) by Weakening(successorInOmega)

    have(
      S(n) ∈ N |- x ∈ app(h, S(n)) <=> inExtIntroImage(h ↾ S(n))(x)
    ) by Weakening(CoreFacts.heightApplication.of(n := S(n)))
    have(
      x ∈ app(h, S(n)) <=> inExtIntroImage(h ↾ S(n))(x)
    ) by Cut(succIsNatStep, lastStep)

    have(
      x ∈ app(h, S(n)) <=> (⊤ /\ inIntroImage(app(h, n))(x))
    ) by Congruence.from(lastStep, unionRangeRes, heightResNonEmptyLemma)

    have(thesis) by Restate.from(lastStep)
  }

  val heightSuccessorStrong = Lemma(
    (isConstructorMono, introFunctionMono, isHeightCore(h), n ∈ N) |-
      x ∈ app(h, S(n)) <=> isConstructor(x)(app(h, n))
  ) {
    assume(isConstructorMono, introFunctionMono, isHeightCore(h))

    def introImageIsConstructor(k: Expr[Ind]): Expr[Prop] =
      inIntroImage(app(h, k))(x) ==> isConstructor(x)(app(h, k))

    val base = have(introImageIsConstructor(∅)) by Tautology.from(heightZero)
    have(n ∈ N ==> (introImageIsConstructor(n) ==> introImageIsConstructor(S(n)))) subproof {
      assume(n ∈ N)
      val inclusion = have(app(h, n) ⊆ app(h, S(n))) by Tautology.from(
        CoreFacts.heightMonotonic.of(m := n, n := S(n)),
        subsetSuccessor,
        successorInOmega
      )
      val constructorMonotonicity = have(isConstructor(x)(app(h, n)) ==> isConstructor(x)(app(h, S(n)))) by
        Tautology.from(inclusion, CoreFacts.isConstructorMonotonic.of(s := app(h, n), t := app(h, S(n))))
      have(thesis) by Tautology.from(constructorMonotonicity, heightSuccessorWeak)
    }
    val step = thenHave(∀(n ∈ N, introImageIsConstructor(n) ==> introImageIsConstructor(S(n)))) by RightForall
    have(∀(n ∈ N, introImageIsConstructor(n))) by Tautology.from(
      base,
      step,
      omegaSuccessorInduction of (P := λ(n, introImageIsConstructor(n)))
    )
    thenHave(n ∈ N ==> introImageIsConstructor(n)) by InstantiateForall(n)
    have(thesis) by Tautology.from(lastStep, heightSuccessorWeak)
  }

  def heightZeroAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      h0: Expr[Ind],
      x0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightZero.of(isConstructor := isConstructor0, h := h0, x := x0)

  def heightSuccessorWeakAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      h0: Expr[Ind],
      n0: Expr[Ind],
      x0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightSuccessorWeak.of(isConstructor := isConstructor0, h := h0, n := n0, x := x0)

  def heightSuccessorStrongAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      h0: Expr[Ind],
      n0: Expr[Ind],
      x0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    heightSuccessorStrong.of(isConstructor := isConstructor0, h := h0, n := n0, x := x0)

  def initialize(): Unit = {
    val _ = heightZero
    val _ = heightSuccessorWeak
    val _ = heightSuccessorStrong
  }
}
