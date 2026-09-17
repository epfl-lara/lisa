package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Functions.Operations.Restriction.notEmpty
import lisa.maths.SetTheory.Ordinals.Integer.{emptyInOmega, omegaSuccessorInduction, selfInSuccessor, subsetSuccessor, successorInOmega}
import lisa.maths.SetTheory.Functions.Operations.Restriction.emptyRestriction
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
    ) by RightSubstEq.withParameters(
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
      ∀(m ∈ N, (m ⊆ n ==> app(h, m) ⊆app(h, n)))
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

    def inductionFormula(k: Expr[Ind]): Expr[Prop] =
      inIntroImage(app(h, k))(x) ==> isConstructor(x)(app(h, k))
    val inductionFormulaN: Expr[Prop] = inductionFormula(n)
    val inductionFormulaSuccN: Expr[Prop] = inductionFormula(S(n))

    // Abbreviations
    val cXn = isConstructor(x)(app(h, n)) // constructor at height n
    val cXsn = isConstructor(x)(app(h, S(n))) // constructor at height S(n)
    val iiN = inIntroImage(app(h, n))(x) // x in the intro-image at height n
    val iiSn = inIntroImage(app(h, S(n)))(x) // x in the intro-image at height S(n)

    // === Base case: inductionFormula(∅) ===
    // inIntroImage(app(h, ∅))(x) = isConstructor(x)(app(h, ∅)) ∨ x ∈ app(h, ∅)
    val baseLeft = have(isConstructor(x)(app(h, ∅)) |- isConstructor(x)(app(h, ∅))) by Hypothesis
    val baseRight = have(x ∈ app(h, ∅) |- ()) by LeftNot(heightZero)
    have(inIntroImage(app(h, ∅))(x) |- isConstructor(x)(app(h, ∅))) by LeftOr(baseLeft, baseRight)
    val zeroCase = thenHave(inductionFormula(∅)) by RightImplies

    // === Induction principle, instantiated at P := λk. inductionFormula(k) ===
    val inductionInstance = have(
      (inductionFormula(∅), ∀(n ∈ N, (inductionFormulaN ==> inductionFormulaSuccN))) |-
        ∀(n ∈ N, inductionFormulaN)
    ) by Weakening(omegaSuccessorInduction of (P := λ(n, inductionFormulaN)))
    val allN = have(
      ∀(n ∈ N, (inductionFormulaN ==> inductionFormulaSuccN)) |- ∀(n ∈ N, inductionFormulaN)
    ) by Cut(zeroCase, inductionInstance)

    // === Successor case ingredients ===
    val succInN = have(n ∈ N |- S(n) ∈ N) by Weakening(successorInOmega)
    val monotonicity = have(
      (n ∈ N, n ⊆ S(n), S(n) ∈ N) |- app(h, n) ⊆ app(h, S(n))
    ) by Weakening(CoreFacts.heightMonotonic.of(n := S(n), m := n))
    have((app(h, n) ⊆ app(h, S(n))) |- cXn ==> cXsn) by
      Weakening(CoreFacts.isConstructorMonotonic.of(s := app(h, n), t := app(h, S(n))))
    val liftImpl = have(n ∈ N |- cXn ==> cXsn) by Cuts(lastStep)(
      monotonicity, subsetSuccessor, succInN
    )

    // === Successor case: (n ∈ N, inductionFormulaN) |- inductionFormulaSuccN ===
    // Right branch: from x ∈ app(h, S(n)) derive cXsn, chaining three implications.

    val mpIH = have((inductionFormulaN, iiN) |- cXn) by Restate
    have((n ∈ N) |- (x ∈ app(h, S(n))) ==> iiN) by Weakening(heightSuccessorWeak)
    val applyWeak = have((n ∈ N, x ∈ app(h, S(n))) |- iiN) by Restate.from(lastStep)
    val getCXn = have((n ∈ N, x ∈ app(h, S(n)), inductionFormulaN) |- cXn) by Cut(applyWeak, mpIH)
    val getCXsn = have((n ∈ N, cXn) |- cXsn) by Restate.from(liftImpl)
    val rightBranch = have((n ∈ N, x ∈ app(h, S(n)), inductionFormulaN) |- cXsn) by
      Cut(getCXn, getCXsn)

    // Left branch and case split on iiSn = cXsn ∨ x ∈ app(h, S(n))
    val leftBranch = have(cXsn |- cXsn) by Hypothesis
    have((n ∈ N, inductionFormulaN, iiSn) |- cXsn) by LeftOr(leftBranch, rightBranch)
    val succCase = thenHave((n ∈ N, inductionFormulaN) |- inductionFormulaSuccN) by RightImplies

    // === Assemble the induction ===
    have(n ∈ N |- inductionFormulaN ==> inductionFormulaSuccN) by RightImplies(succCase)
    thenHave(n ∈ N ==> (inductionFormulaN ==> inductionFormulaSuccN)) by RightImplies
    thenHave(∀(n ∈ N, (inductionFormulaN ==> inductionFormulaSuccN))) by RightForall
    have(∀(n ∈ N, inductionFormulaN)) by Cut(lastStep, allN)
    thenHave(n ∈ N ==> inductionFormulaN) by InstantiateForall(n)
    val forward = thenHave(n ∈ N |- iiN ==> cXn) by Restate

    // backward : isConstructor  ⟹  intro-image (trivial, since cXn is a disjunct of iiN)
    val backward = have(n ∈ N |- cXn ==> iiN) by Restate


    have(n ∈ N |- iiN <=> cXn) by RightIff(forward, backward)
    have(n ∈ N |- (x ∈ app(h, S(n)) <=> cXn)) by Congruence.from(heightSuccessorWeak,lastStep)
    have(thesis) by Restate.from(lastStep)
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
