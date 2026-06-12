package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.{CoreFacts, SuccessorFacts, UniquenessFacts}

final class HeightConstructors[N <: Arity](
  base: HeightADT[N],
  constructors: Seq[HeightConstructorData],
  heightStageSet: HeightStageSet[N],
  isConstructor: Expr[Ind >>: Ind >>: Prop]
) {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    base.inIntroImage(s)(y)

  private def constructorPredicate(
      c: HeightConstructorData,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables, wellTypedFormula(c.signature)(s) /\ (x === c.term))
    
  val heightExists = Lemma(exists(h, base.isHeight(h))) {
    have(thesis) by Restate.from(heightStageSet.heightExists)
  }

  /**
   *  Lemma --- If two functions are the height function then they are the same.
   *
   *  `f = height /\ h = height => f = h`
   */
  val heightUniqueness = Lemma((base.isHeight(f), base.isHeight(h)) |- f === h) {

    have(thesis) by Tautology.from(
      UniquenessFacts.uniquenessAt(isConstructor, f, h),
      introFunctionMonoHyp,
      base.heightIsCore of (h := f),
      base.heightIsCore of (h := h)
    )
  }

  val heightExistsOne = Lemma(existsOne(h, base.isHeight(h))) {
    
    val existencePart = have(∃(h, base.isHeight(h))) by
      Restate.from(heightExists of (h := h))

    have(base.isHeight(f) /\ base.isHeight(h) ==> (f === h)) by
      Restate.from(heightUniqueness)
    thenHave(
      ∀(h, base.isHeight(f) /\ base.isHeight(h) ==> (f === h))
    ) by RightForall
    val uniquenessAll = thenHave(
      ∀(f, ∀(h, base.isHeight(f) /\ base.isHeight(h) ==> (f === h)))
    ) by RightForall

    have(
      ∃(h, base.isHeight(h)) /\
        ∀(f, ∀(h, base.isHeight(f) /\ base.isHeight(h) ==> (f === h)))
    ) by Tautology.from(existencePart, uniquenessAll)

    have(thesis) by Tautology.from(
      lastStep,
      existsOneAlternativeDefinition of (x := h, P := λ(h, base.isHeight(h)))
    )
  }

  /**
   *  Lemma --- The introduction function is monotonic with respect to set inclusion.
   *
   *  `s ⊆ t |- introductionFunction(s) ⊆ introductionFunction(t)`
   */
  private[ADTv2] lazy val introductionFunctionMononotic = Lemma(
    subset(s, t) |-
      inIntroImage(s)(x) ==> inIntroImage(t)(x)
  ) {
    val subsetST = s ⊆ t
    val isConstructorXS = isConstructor(x)(s)
    val isConstructorXT = isConstructor(x)(t)

    have(s ⊆ t |- forall(z, in(z, s) ==> in(z, t))) by
      Congruence.from(subsetAxiom of (x := s, y := t))
    val subsetElimination = thenHave(s ⊆ t |- in(z, s) ==> in(z, t)) by
      InstantiateForall(z)

    val isConstructorXSImpliesT =
      for c <- constructors yield
        val labelEq = x === c.term
        val isConstructorCXS = constructorPredicate(c, x, s)
        val isConstructorCXT = constructorPredicate(c, x, t)
        val varsWellTypedS = wellTypedFormula(c.signature)(s)
        val varsWellTypedT = wellTypedFormula(c.signature)(t)

        if c.arity == 0 then
          have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
        else
          val andSeq =
            for (v, ty) <- c.signature
            yield have((subsetST, varsWellTypedS) |- in(v, ty.getOrElse(t))) by
              Weakening(subsetElimination of (z := v))
          val expandingDomain = have((subsetST, varsWellTypedS) |- varsWellTypedT) by
            RightAnd(andSeq*)
          val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
          have((subsetST, varsWellTypedS, labelEq) |- varsWellTypedT /\ labelEq) by
            RightAnd(expandingDomain, weakeningLabelEq)

          val existsCXS = existsSeq(c.variables, varsWellTypedS /\ labelEq)
          val existsCXT = existsSeq(c.variables, varsWellTypedT /\ labelEq)

          thenHave((subsetST, varsWellTypedS, labelEq) |- existsCXT) by
            QuantifiersIntro(c.variables)
          thenHave((subsetST, varsWellTypedS /\ labelEq) |- existsCXT) by LeftAnd
          thenHave((subsetST, existsCXS) |- existsCXT) by QuantifiersIntro(c.variables)
          have((subsetST, isConstructorCXS) |- isConstructorXT) by Tautology.from(lastStep)

    val constructorBranch =
      if constructors.isEmpty then
        have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
      else
        have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(
          isConstructorXSImpliesT*
        )

    val constructorCase = have((subsetST, isConstructorXS) |- inIntroImage(t)(x)) by
      Tautology.from(constructorBranch)

    val subsetEliminationX = have(s ⊆ t |- in(x, s) ==> in(x, t)) by
      Restate.from(subsetElimination of (z := x))
    have((subsetST, in(x, s)) |- in(x, t)) by Tautology.from(subsetEliminationX)
    val membershipCase = have((subsetST, in(x, s)) |- inIntroImage(t)(x)) by
      Tautology.from(lastStep)

    have((subsetST, inIntroImage(s)(x)) |- inIntroImage(t)(x)) by
      Tautology.from(constructorCase, membershipCase)
    thenHave(thesis) by RightImplies
  }

  private lazy val introFunctionMonoHyp: THM = Lemma(
    CoreFacts.introFunctionMono.substitute(CoreFacts.isConstructor := isConstructor)
  ) {
    have(introductionFunctionMononotic.statement) by
      Restate.from(introductionFunctionMononotic)
    thenHave(subset(s, t) |- forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))) by
      RightForall
    thenHave(subset(s, t) ==> forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))) by
      RightImplies
    thenHave(
      forall(t, subset(s, t) ==> forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x)))
    ) by RightForall
    thenHave(thesis) by RightForall
  }

  private lazy val isConstructorMonoHyp: THM = Lemma(
    CoreFacts.isConstructorMono.substitute(CoreFacts.isConstructor := isConstructor)
  ) {
    val subsetST = s ⊆ t
    val isConstructorXS = isConstructor(x)(s)
    val isConstructorXT = isConstructor(x)(t)

    val isConstructorXSImpliesT =
      for c <- constructors yield
        val labelEq = x === c.term
        val isConstructorCXS = constructorPredicate(c, x, s)
        val isConstructorCXT = constructorPredicate(c, x, t)
        val varsWellTypedS = wellTypedFormula(c.signature)(s)
        val varsWellTypedT = wellTypedFormula(c.signature)(t)

        if c.arity == 0 then
          have((subsetST, isConstructorCXS) |- isConstructorCXT) by Restate
          have((subsetST, isConstructorCXS) |- isConstructorXT) by Tautology.from(lastStep)
        else
          have(s ⊆ t |- forall(z, in(z, s) ==> in(z, t))) by
            Congruence.from(subsetAxiom of (x := s, y := t))
          val subsetElimination = thenHave(s ⊆ t |- in(z, s) ==> in(z, t)) by
            InstantiateForall(z)
          val andSeq =
            for (v, ty) <- c.signature
            yield have((subsetST, varsWellTypedS) |- in(v, ty.getOrElse(t))) by
              Weakening(subsetElimination of (z := v))
          val expandingDomain = have((subsetST, varsWellTypedS) |- varsWellTypedT) by
            RightAnd(andSeq*)
          val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
          have((subsetST, varsWellTypedS, labelEq) |- varsWellTypedT /\ labelEq) by
            RightAnd(expandingDomain, weakeningLabelEq)

          thenHave((subsetST, varsWellTypedS, labelEq) |- isConstructorCXT) by
            QuantifiersIntro(c.variables)
          thenHave((subsetST, varsWellTypedS /\ labelEq) |- isConstructorCXT) by LeftAnd
          thenHave((subsetST, isConstructorCXS) |- isConstructorCXT) by
            QuantifiersIntro(c.variables)
          thenHave((subsetST, isConstructorCXS) |- isConstructorXT) by Weakening

    val constructorBranch =
      if constructors.isEmpty then
        have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
      else
        have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(
          isConstructorXSImpliesT*
        )

    have((subsetST, isConstructorXS) |- isConstructorXT) by Restate.from(constructorBranch)
    thenHave(subsetST |- isConstructorXS ==> isConstructorXT) by RightImplies
    thenHave(subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t))) by Restate
    thenHave(forall(x, subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t)))) by
      RightForall
    thenHave(forall(t, forall(x, subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t))))) by
      RightForall
    thenHave(thesis) by RightForall
  }

  /**
   *  Lemma --- The extended introduction function is monotonic with respect to set
   *  inclusion.
   */
  private[ADTv2] val extIntroMonotonic = Lemma(
    subset(f, g) |-
      base.inExtIntroImage(f)(x) ==>
      base.inExtIntroImage(g)(x)
  ) {
    have(thesis) by Tautology.from(
      introFunctionMonoHyp,
      CoreFacts.extIntroMonotonicAt(isConstructor, f, g, x)
    )
  }

  /**
   *  Lemma --- The height function is monotonic.
   */
  val heightMonotonic = Lemma(
    (base.isHeight(h), in(n, N), in(m, N), subset(m, n)) |- subset(app(h, m), app(h, n))
  ) {
    have(thesis) by Tautology.from(
      base.heightIsCore,
      introFunctionMonoHyp,
      CoreFacts.heightMonotonicAt(isConstructor, h, n, m)
    )
  }

  val heightMembershipMonotonic = Lemma(
    (base.isHeight(h), in(n, N), in(m, N), subset(m, n), in(x, app(h, m))) |- in(x, app(h, n))
  ) {
    val hIsHeight = assume(base.isHeight(h))
    val nInN = assume(in(n, N))
    val mInN = assume(in(m, N))
    val mSubN = assume(subset(m, n))
    val xInHm = assume(in(x, app(h, m)))

    val hSubset = have(subset(app(h, m), app(h, n))) by
      Tautology.from(hIsHeight, nInN, mInN, mSubN, heightMonotonic)

    have(in(x, app(h, n))) by Tautology.from(
      hSubset,
      xInHm,
      Subset.membership of (x := app(h, m), y := app(h, n), z := x)
    )
    thenHave(thesis) by Restate
  }

  val heightSuccessorInclusion = Lemma(
    (base.isHeight(h), in(n, N), in(x, app(h, n))) |- in(x, app(h, successor(n)))
  ) {
    val hIsHeight = assume(base.isHeight(h))
    val nInN = assume(in(n, N))
    val xInHn = assume(in(x, app(h, n)))
    val succInN = have(in(successor(n), N)) by Tautology.from(
      successorIsNat of (n := n),
      nInN
    )
    have(in(x, app(h, successor(n)))) by Tautology.from(
      hIsHeight,
      succInN,
      nInN,
      subsetSuccessor of (n := n),
      xInHn,
      heightMembershipMonotonic of (m := n, n := successor(n))
    )
    thenHave(thesis) by Restate
  }

  /**
   *  Lemma --- The set of elements of height n + 1 is the introduction image of height n.
   */
  val heightSuccessorWeak = Lemma(
    (base.isHeight(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> inIntroImage(app(h, n))(x)
  ) {
    have(thesis) by Tautology.from(
      base.heightIsCore,
      introFunctionMonoHyp,
      SuccessorFacts.heightSuccessorWeakAt(isConstructor, h, n, x)
    )
  }

  /**
   *  Base case used by the internal nat induction in heightSuccessorStrong.
   */
  private[ADTv2] lazy val introductionImageAtHeightZeroIsConstructor = Lemma(
    base.isHeight(h) |-
      inIntroImage(app(h, ∅))(x) ==> isConstructor(x)(app(h, ∅))
  ) {
    val isContructorXHEmptySet = isConstructor(x)(app(h, ∅))
    val baseCaseLeft = have(isContructorXHEmptySet |- isContructorXHEmptySet) by
      Hypothesis
    val baseCaseRight = have((base.isHeight(h), in(x, app(h, ∅))) |- ()) by
      Restate.from(base.heightZero)
    have((base.isHeight(h), inIntroImage(app(h, ∅))(x)) |- isContructorXHEmptySet) by
      LeftOr(baseCaseLeft, baseCaseRight)
    thenHave(
      base.isHeight(h) |-
        inIntroImage(app(h, ∅))(x) ==> isContructorXHEmptySet
    ) by RightImplies
  }

  private[ADTv2] lazy val heightSuccessorStrong = Lemma(
    (base.isHeight(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> isConstructor(x)(app(h, n))
  ) {
    have(thesis) by Tautology.from(
      base.heightIsCore,
      introFunctionMonoHyp,
      isConstructorMonoHyp,
      SuccessorFacts.heightSuccessorStrongAt(isConstructor, h, n, x)
    )
  }
}
