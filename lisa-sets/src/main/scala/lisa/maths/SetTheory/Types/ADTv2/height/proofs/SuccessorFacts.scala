package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UnionRangeCollapse.unionRangeCollapse
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.CoreFacts.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*

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
        unionRange(h ↾ successor(n)) === app(h, n)
    ) by Tautology.from(lastStep, unionRangeCollapse)

    val succIsNatStep = have((isHeightCore(h), in(n, N)) |- in(successor(n), N)) by
      Tautology.from(successorIsNat)

    have(
      (isHeightCore(h), in(n, N)) |-
        in(x, app(h, successor(n))) <=>
        inExtIntroImage(h ↾ successor(n))(x)
    ) by Cut(succIsNatStep, CoreFacts.heightApplication.of(n := successor(n)))

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

  val heightSuccessorStrong = Lemma(
    (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> isConstructor(x)(app(h, n))
  ) {
    val forward = have(
      (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
        inIntroImage(app(h, n))(x) ==> isConstructor(x)(app(h, n))
    ) subproof {
      def inductionFormula(k: Expr[Ind]): Expr[Prop] =
        inIntroImage(app(h, k))(x) ==> isConstructor(x)(app(h, k))
      val inductionFormulaN: Expr[Prop] = inductionFormula(n)
      val inductionFormulaSuccN: Expr[Prop] = inductionFormula(successor(n))

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
        val isConstructorXHSuccN = isConstructor(x)(app(h, successor(n)))

        have(in(n, N) |- in(successor(n), N)) by Cut(
          successorIsNat,
          equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N))
        )
        have(
          (introFunctionMono, isHeightCore(h), in(n, N), subset(n, successor(n))) |-
            subset(app(h, n), app(h, successor(n)))
        ) by Cut(lastStep, CoreFacts.heightMonotonic.of(n := successor(n), m := n))
        val heightSubset = have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N)) |-
            subset(app(h, n), app(h, successor(n)))
        ) by Tautology.from(subsetSuccessor, lastStep)

        val liftConstructorHeight = have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N), isConstructorXHN) |-
            isConstructorXHSuccN
        ) by Tautology.from(
          heightSubset,
          CoreFacts.isConstructorMonotonic.of(s := app(h, n), t := app(h, successor(n)))
        )

        val heightSuccessorWeakForward = have(
          (isConstructorMono, introFunctionMono, isHeightCore(h), in(n, N), in(x, app(h, successor(n)))) |-
            inIntroImage(app(h, n))(x)
        ) by Tautology.from(
          heightSuccessorWeak,
          equivalenceApply of (
            p1 := in(x, app(h, successor(n))),
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
            in(x, app(h, successor(n))),
            inductionFormulaN
          ) |- isConstructorXHN
        ) by Cut(heightSuccessorWeakForward, lastStep)

        val right = have(
          (
            isConstructorMono,
            introFunctionMono,
            isHeightCore(h),
            in(n, N),
            in(x, app(h, successor(n))),
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
            inIntroImage(app(h, successor(n)))(x)
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
