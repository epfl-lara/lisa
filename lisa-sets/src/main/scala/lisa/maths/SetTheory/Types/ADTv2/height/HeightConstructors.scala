package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Ordinals.Integer.{subsetSuccessor, successorInOmega}
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.CoreFacts
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.SuccessorFacts
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.UniquenessFacts
import lisa.utils.prooflib.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts
import lisa.utils.prooflib.ProofTacticLib.Arity

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


  /**
   *  Lemma --- If two functions are the height function then they are the same.
   *
   *  `f = height /\ h = height => f = h`
   */
  val heightUniqueness = Lemma((base.isHeight(f), base.isHeight(h)) |- f === h) {

    have(thesis) by Cuts(UniquenessFacts.uniquenessAt(isConstructor, f, h))(
      introFunctionMonoHyp,
      base.heightIsCore of (h := f),
      base.heightIsCore of (h := h)
    )
  }

  val heightExistsOne = Lemma(existsOne(h, base.isHeight(h))) {

    val existencePart = have(∃(h, base.isHeight(h))) by
      Restate.from(heightStageSet.heightExists of (h := h))

    have(base.isHeight(f) /\ base.isHeight(h) ==> (f === h)) by
      Restate.from(heightUniqueness)
    val uniquenessAll = thenHave(
      ∀(f, ∀(h, base.isHeight(f) /\ base.isHeight(h) ==> (f === h)))
    ) by Generalize

    have(
      ∃(h, base.isHeight(h)) /\
        ∀(f, ∀(h, base.isHeight(f) /\ base.isHeight(h) ==> (f === h)))
    ) by RightAnd(existencePart, uniquenessAll)

    thenHave(thesis) by Substitute(
      existsOneAlternativeDefinition of (x := h, P := λ(h, base.isHeight(h)))
    )
  }

  /**
   *  Lemma --- The introduction function is monotonic with respect to set inclusion.
   *
   *  `s ⊆ t |- introductionFunction(s) ⊆ introductionFunction(t)`
   *
   * Derived from `isConstructorMonoHyp` (the concrete `isConstructor` monotonicity) plus
   * subset elimination for the membership disjunct: `inIntroImage` is just
   * `isConstructor(x)(s) \/ in(x, s)`, so monotonicity of each disjunct lifts to the whole.
   * This avoids re-proving the constructor-by-constructor argument that already lives in
   * `isConstructorMonoHyp`.
   */
  private lazy val introFunctionMonoHyp: THM = Lemma(
    CoreFacts.introFunctionMono.substitute(CoreFacts.isConstructor := isConstructor)
  ) {
    val ctorMono = have(subset(s, t) |- isConstructor(x)(s) ==> isConstructor(x)(t)) by Cut(
      isConstructorMonoHyp,
      CoreFacts.isConstructorMonotonic.of(CoreFacts.isConstructor := isConstructor)
    )
    have(subset(s, t) |- forall(z, in(z, s) ==> in(z, t))) by
      Congruence.from(subsetAxiom of (x := s, y := t))
    val memMono = thenHave(subset(s, t) |- in(x, s) ==> in(x, t)) by InstantiateForall(x)

    have(subset(s, t) |- inIntroImage(s)(x) ==> inIntroImage(t)(x)) by
      Tautology.from(ctorMono, memMono)
    thenHave(subset(s, t) |- forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))) by RightForall


    thenHave(subset(s, t) ==> forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))) by RightImplies
    thenHave(thesis) by Generalize
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
        val isConstructorCXS = heightStageSet.constructorPredicate(c, x, s)
        val isConstructorCXT = heightStageSet.constructorPredicate(c, x, t)
        val varsWellTypedS = wellTypedFormula(c.signature)(s)
        val varsWellTypedT = wellTypedFormula(c.signature)(t)

        if c.arity == 0 then
          have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
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
      if constructors.isEmpty then have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
      else
        have((subsetST, isConstructorXS) |- isConstructorXT) by 
          LeftOr(isConstructorXSImpliesT*)

    have(subset(s, t) ==> (isConstructor(x)(s) ==> isConstructor(x)(t))) by Restate.from(constructorBranch)
    thenHave(thesis) by Generalize
  }

  /**
   *  Lemma --- The height function is monotonic.
   */
  val heightMonotonic = Lemma(
    (base.isHeight(h), in(n, N), in(m, N), subset(m, n)) |- subset(app(h, m), app(h, n))
  ) {
    have(thesis) by Cuts(CoreFacts.heightMonotonicAt(isConstructor, h, n, m))(
      base.heightIsCore,
      introFunctionMonoHyp
    )
  }

  val heightMembershipMonotonic = Lemma(
    (base.isHeight(h), n ∈ N, m ∈ N, m ⊆ n, x ∈ app(h, m)) |- in(x, app(h, n))
  ) {
    assume(base.isHeight(h), n ∈ N, m ∈ N, m ⊆ n, x ∈ app(h, m))

    val hSubset = have(app(h, m) ⊆ app(h, n)) by Weakening(heightMonotonic)

    have(x ∈ app(h, m) ==> x ∈ app(h, n)) by Cut(
      hSubset,
      Subset.membership of (x := app(h, m), y := app(h, n), z := x)
    )
    thenHave(thesis) by Restate
  }

  val heightSuccessorInclusion = Lemma(
    (base.isHeight(h), in(n, N), in(x, app(h, n))) |- in(x, app(h, S(n)))
  ) {
    assume(base.isHeight(h))
    val nInN = assume(in(n, N))
    assume(in(x, app(h, n)))
    val succInN = have(in(S(n), N)) by Substitute(successorInOmega of (n := n))(nInN)
    have(in(x, app(h, S(n)))) by Cuts(heightMembershipMonotonic of (m := n, n := S(n)))(
      succInN,
      subsetSuccessor of (n := n)
    )
    thenHave(thesis) by Restate
  }

  /**
   *  Lemma --- The set of elements of height n + 1 is the introduction image of height n.
   */
  val heightSuccessorWeak = Lemma(
    (base.isHeight(h), in(n, N)) |-
      in(x, app(h, S(n))) <=> inIntroImage(app(h, n))(x)
  ) {
    have(thesis) by Cuts(SuccessorFacts.heightSuccessorWeakAt(isConstructor, h, n, x))(
      base.heightIsCore,
      introFunctionMonoHyp
    )
  }

  private[ADTv2] lazy val heightSuccessorStrong = Lemma(
    (base.isHeight(h), in(n, N)) |-
      in(x, app(h, S(n))) <=> isConstructor(x)(app(h, n))
  ) {
    have(thesis) by Cuts(SuccessorFacts.heightSuccessorStrongAt(isConstructor, h, n, x))(
      base.heightIsCore,
      introFunctionMonoHyp,
      isConstructorMonoHyp
    )
  }
}
