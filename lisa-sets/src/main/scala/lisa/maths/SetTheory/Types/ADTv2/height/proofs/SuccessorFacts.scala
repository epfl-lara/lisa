package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Functions.Operations.Restriction.emptyRestriction
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.CoreFacts._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.nInSuccN
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.natInduction
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.subsetSuccessor
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.successorIsNat
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.zeroIsNat
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UnionRangeCollapse.unionRangeCollapse
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems._

private[height] object SuccessorFacts {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  val heightZero = Lemma(isHeightCore(h) |- !in(x, app(h, ∅))) {
    have(
      isHeightCore(h) |-
        in(x, app(h, ∅)) <=>
        inExtIntroImage(h ↾ ∅)(x)
    ) by Cut(zeroIsNat, CoreFacts.heightApplication.of(n := ∅))
    thenHave(
      (h ↾ ∅ === ∅, isHeightCore(h)) |- !in(x, app(h, ∅))
    ) by RightSubstEq.withParameters(
      List((h ↾ ∅, ∅)),
      (Seq(s), in(x, app(h, ∅)) <=> inExtIntroImage(s)(x))
    )
    have(thesis) by Cut(emptyRestriction of (f := h), lastStep)
  }

  val heightSuccessorWeak = Lemma(
    (introFunctionMono, isHeightCore(h), in(n, N)) |-
      in(x, app(h, S(n))) <=> inIntroImage(app(h, n))(x)
  ) {
    val heightResNonEmpty: Expr[Prop] = !(h ↾ S(n) === ∅)

    val coreTyping = have(
      (isHeightCore(h), in(n, N)) |- function(h) /\ (dom(h) === N)
    ) by Tautology
    val nInNFact = have((isHeightCore(h), in(n, N)) |- in(n, N)) by Hypothesis
    val domEq = have((isHeightCore(h), in(n, N)) |- dom(h) === N) by Tautology.from(coreTyping)
    val nInDomH = have((isHeightCore(h), in(n, N)) |- in(n, dom(h))) by Congruence.from(nInNFact, domEq)
    val nInSucc = have((isHeightCore(h), in(n, N)) |- in(n, S(n))) by
      Tautology.from(nInSuccN of (n := n))

    val heightResNonEmptyLemma = have((isHeightCore(h), in(n, N)) |- heightResNonEmpty) by
      Tautology.from(
        coreTyping,
        nInDomH,
        nInSucc,
        restrictedFunctionNotEmpty of (f := h, x := n, d := S(n))
      )

    have(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N), subset(m, n)) |-
        subset(app(h, m), app(h, n))
    ) by Restate.from(CoreFacts.heightMonotonic)
    thenHave(
      (introFunctionMono, isHeightCore(h), in(n, N), in(m, N)) |-
        subset(m, n) ==> subset(app(h, m), app(h, n))
    ) by RightImplies.withParameters(subset(m, n), subset(app(h, m), app(h, n)))
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
        unionRange(h ↾ S(n)) === app(h, n)
    ) by Tautology.from(lastStep, unionRangeCollapse)

    val succIsNatStep = have((isHeightCore(h), in(n, N)) |- in(S(n), N)) by
      Tautology.from(successorIsNat)

    have(
      (isHeightCore(h), in(n, N)) |-
        in(x, app(h, S(n))) <=>
        inExtIntroImage(h ↾ S(n))(x)
    ) by Cut(succIsNatStep, CoreFacts.heightApplication.of(n := S(n)))

    thenHave(
      (
        isHeightCore(h),
        in(n, N),
        unionRange(h ↾ S(n)) === app(h, n)
      ) |-
        in(x, app(h, S(n))) <=>
        heightResNonEmpty /\ inIntroImage(app(h, n))(x)
    ) by RightSubstEq.withParameters(
      List((unionRange(h ↾ S(n)), app(h, n))),
      (
        Seq(s),
        in(x, app(h, S(n))) <=>
          (heightResNonEmpty /\ inIntroImage(s)(x))
      )
    )

    have(
      (introFunctionMono, isHeightCore(h), in(n, N)) |-
        in(x, app(h, S(n))) <=> heightResNonEmpty /\ inIntroImage(app(h, n))(x)
    ) by Cut(unionRangeRes, lastStep)

    have(
      (introFunctionMono, isHeightCore(h), in(n, N), heightResNonEmpty) |-
        in(x, app(h, S(n))) <=> inIntroImage(app(h, n))(x)
    ) by Cut(lastStep, equivalenceAnd of (
      p1 := in(x, app(h, S(n))),
      p2 := heightResNonEmpty,
      p3 := inIntroImage(app(h, n))(x)
    ))

    have(thesis) by Cut(heightResNonEmptyLemma, lastStep)
  }

  val heightSuccessorStrong = Lemma(
    (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
      in(x, app(h, S(n))) <=> isConstructor(x)(app(h, n))
  ) {
    val forward = have(
      (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
        inIntroImage(app(h, n))(x) ==> isConstructor(x)(app(h, n))
    ) subproof {
      def inductionFormula(k: Expr[Ind]): Expr[Prop] =
        inIntroImage(app(h, k))(x) ==> isConstructor(x)(app(h, k))
      val inductionFormulaN: Expr[Prop] = inductionFormula(n)
      val inductionFormulaSuccN: Expr[Prop] = inductionFormula(S(n))

      val zeroCase = have(
        (isConstructorMono, introFunctionMono, isHeightCore(h)) |- inductionFormula(∅)
      ) subproof {
        val isConstructorXHEmptySet = isConstructor(x)(app(h, ∅))
        val baseCaseLeft = have(isConstructorXHEmptySet |- isConstructorXHEmptySet) by
          Hypothesis
        val baseCaseRight = have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(x, app(h, ∅))) |- ()
        ) by Tautology.from(heightZero)
        have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), inIntroImage(app(h, ∅))(x)) |- isConstructorXHEmptySet
        ) by LeftOr(baseCaseLeft, baseCaseRight)
        thenHave(thesis) by RightImplies
      }

      val inductiveCaseRemaining = have(
        (
          isConstructorMono,
          introFunctionMono,
          isHeightCore(h),
          forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))
        ) |- forall(n, in(n, N) ==> inductionFormulaN)
      ) by Cut(zeroCase, natInduction of (P := lambda(n, inductionFormulaN)))

      val succCase = have(
        (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N), inductionFormulaN) |- inductionFormulaSuccN
      ) subproof {
        val isConstructorXHN = isConstructor(x)(app(h, n))
        val isConstructorXHSuccN = isConstructor(x)(app(h, S(n)))

        have(in(n, N) |- in(S(n), N)) by Cut(
          successorIsNat,
          equivalenceApply of (p1 := in(n, N), p2 := in(S(n), N))
        )
        have(
          (introFunctionMono, isHeightCore(h), in(n, N), subset(n, S(n))) |-
            subset(app(h, n), app(h, S(n)))
        ) by Cut(lastStep, CoreFacts.heightMonotonic.of(n := S(n), m := n))
        val heightSubset = have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
            subset(app(h, n), app(h, S(n)))
        ) by Tautology.from(subsetSuccessor, lastStep)

        val liftConstructorHeight = have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N), isConstructorXHN) |-
            isConstructorXHSuccN
        ) by Tautology.from(
          heightSubset,
          CoreFacts.isConstructorMonotonic.of(s := app(h, n), t := app(h, S(n)))
        )

        val heightSuccessorWeakForward = have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N), in(x, app(h, S(n)))) |-
            inIntroImage(app(h, n))(x)
        ) by Tautology.from(
          heightSuccessorWeak,
          equivalenceApply of (
            p1 := in(x, app(h, S(n))),
            p2 := inIntroImage(app(h, n))(x)
          )
        )

        have((inductionFormulaN, inIntroImage(app(h, n))(x)) |- isConstructorXHN) by Restate
        have(
          (
            isConstructorMono,
            introFunctionMono,
            isHeightCore(h),
            in(n, N),
            in(x, app(h, S(n))),
            inductionFormulaN
          ) |- isConstructorXHN
        ) by Cut(heightSuccessorWeakForward, lastStep)

        val right = have(
          (
            isConstructorMono,
            introFunctionMono,
            isHeightCore(h),
            in(n, N),
            in(x, app(h, S(n))),
            inductionFormulaN
          ) |- isConstructorXHSuccN
        ) by Cut(lastStep, liftConstructorHeight)
        val left = have(isConstructorXHSuccN |- isConstructorXHSuccN) by Hypothesis

        have(
          (
            isConstructorMono,
            introFunctionMono,
            isHeightCore(h),
            in(n, N),
            inductionFormulaN,
            inIntroImage(app(h, S(n)))(x)
          ) |- isConstructorXHSuccN
        ) by LeftOr(left, right)
        thenHave(thesis) by RightImplies
      }

      have(
        (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |- inductionFormulaN
      ) subproof {
        have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |- inductionFormulaN ==> inductionFormulaSuccN
        ) by RightImplies(succCase)
        thenHave(
          (isConstructorMono, introFunctionMono, isHeightCore(h)) |- in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)
        ) by RightImplies
        thenHave(
          (isConstructorMono, introFunctionMono, isHeightCore(h)) |- forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))
        ) by RightForall
        have(
          (isConstructorMono, introFunctionMono, isHeightCore(h)) |- forall(n, in(n, N) ==> inductionFormulaN)
        ) by Cut(lastStep, inductiveCaseRemaining)
        thenHave(
          (isConstructorMono, introFunctionMono, isHeightCore(h)) |- in(n, N) ==> inductionFormulaN
        ) by InstantiateForall(n)
        have(thesis) by Tautology.from(lastStep)
      }
    }

    val backward = have(
      (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
        isConstructor(x)(app(h, n)) ==> inIntroImage(app(h, n))(x)
    ) by Restate

    have(
      (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
        inIntroImage(app(h, n))(x) <=> isConstructor(x)(app(h, n))
    ) by RightIff(forward, backward)
    have(thesis) by Tautology.from(equivalenceRewriting, lastStep, heightSuccessorWeak)
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
