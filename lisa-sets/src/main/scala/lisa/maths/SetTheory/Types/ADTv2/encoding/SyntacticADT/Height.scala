package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*

private[encoding] trait SyntacticADTHeight[N <: Arity]
    extends SyntacticADTIntroduction[N] {
  this: SyntacticADT[N] =>

  private val P = variable[Ind >>: Prop]

  // *******************
  // * HEIGHT FUNCTION *
  // *******************

  /**
   *  Lemma --- The extended introduction function is monotonic with respect to set
   *  inclusion.
   *
   *  `f ⊆ g |- extendedIntroductionFunction(f) ⊆ extendedIntroductionFunction(g)`
   */
  private[encoding] val extendedIntroductionFunctionMonotonic = Lemma(
    subset(f, g) |-
      isInExtendedIntroductionFunctionImage(f)(x) ==>
      isInExtendedIntroductionFunctionImage(g)(x)
  ) {

    // STEP 0: Caching
    val introFunUnionRangeF = isInIntroductionFunctionImage(unionRange(f))(x)
    val introFunUnionRangeG = isInIntroductionFunctionImage(unionRange(g))(x)

    // STEP 1: Instantiate monotonicity of the introduction function for the union of the ranges of f and g
    have(subset(f, g) |- introFunUnionRangeF ==> introFunUnionRangeG) by Cut(
      unionRangeMonotonic,
      introductionFunctionMononotic of (s := unionRange(f), t := unionRange(g))
    )
    val left = thenHave((subset(f, g), introFunUnionRangeF) |- introFunUnionRangeG) by
      Restate

    // STEP 2: Conclude by applying the conjuction on both sides
    have(
      (subset(f, g), !(f === ∅), introFunUnionRangeF) |-
        isInExtendedIntroductionFunctionImage(g)(x)
    ) by RightAnd(left, subsetNotEmpty of (x := f, y := g))
  }

  /**
   *  Lemma --- There exists a unique height function for this ADT.
   *
   *  `∃!h. h = height`
   *
   *  TODO: Prove this using transfinite recursion
   */
  private[encoding] val heightFunUniqueness = Axiom(existsOne(h, isHeight(h)))

  /**
   *  Lemma --- The height function exists.
   *
   *  `∃h. h = height`
   */
  private[encoding] val heightFunctionExistence = Lemma(exists(h, isHeight(h))) {
    have(thesis) by Cut(
      heightFunUniqueness.asInstanceOf,
      lisa.maths.Quantifiers.existsOneImpliesExists of
        (P := lam(h, isHeight(h)))
    )
  }

  /**
   *  Lemma --- If two functions are the height function then they are the same.
   *
   *  `f = height /\ h = height => f = h`
   */
  private[encoding] val heightFunctionUniqueness2 =
    Lemma((isHeight(f), isHeight(h)) |- f === h) {
      have(thesis) by Cut(
        heightFunUniqueness,
        existsOneUniqueness of (P := lam(h, isHeight(h)), x := f, y := h)
      )
    }

  /**
   *  Lemma --- The height function is not empty.
   *
   *  `height ≠ ∅`
   */
  private[encoding] val heightFunctionNonEmpty =
    Lemma(isHeight(h) |- !(h === ∅)) {
      // The proof goes by contradiction. If the height function is empty then its domain is empty as well.
      // This would imply that the set of natural numbers is empty, which is a contradiction.
      val heightDomEqN = have(isHeight(h) |- relationDomain(h) === N) by
        Tautology.from(isHeight.definition)
      val domRefl = have(relationDomain(h) === relationDomain(h)) by Congruence

      have(N === ∅ |- ()) by Restate.from(natNotEmpty)
      thenHave(
        (
          relationDomain(h) === ∅,
          relationDomain(h) === N,
          relationDomain(h) === relationDomain(h)
        ) |- ()
      ) by LeftSubstEq.withParameters(
        List((relationDomain(h), ∅), (relationDomain(h), N)),
        (Seq(x, y), y === x)
      )
      // thenHave(
      //   (relationDomain(h) === N, relationDomain(h) === relationDomain(h)) |-
      //     !(relationDomain(h) === ∅)
      // ) by Tautology
      have(
        (
          isHeight(h),
          relationDomain(h) === ∅,
          relationDomain(h) === relationDomain(h)
        ) |- ()
      ) by Cut(heightDomEqN, lastStep)
      thenHave(
        (isHeight(h), relationDomain(h) === relationDomain(h)) |-
          !(relationDomain(h) === ∅)
      ) by RightNot
      have(isHeight(h) |- !(relationDomain(h) === ∅)) by Cut(domRefl, lastStep)
      have(
        isHeight(h) |- !(h === ∅)
      ) by Tautology.from(lastStep, nonEmptyDomain)
      thenHave(thesis) by Restate
    }

  /**
   *  Lemma --- The set of elements of height n or below is the image of the extended
   *  introduction function under the height function restricted to n (consequence of
   *  transfinite recursion).
   *
   *  `height(n) = extendedIntroductionFunction(height | n)`
   */
  private[encoding] val heightApplication = Lemma(
    (isHeight(h), in(n, N)) |-
      in(x, app(h, n)) <=>
      isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)
  ) {

    // Caching
    val extendedIntroFunRestrictedFunM =
      isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)
    val heightFunApplicationDef = forall(
      n,
      in(n, N) ==> forall(x, in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM)
    )

    // Unfold the dedicated height-function predicate and instantiate the specification.
    have(isHeight(h) |- heightFunApplicationDef) by
      Tautology.from(isHeight.definition)
    thenHave(
      (isHeight(h), in(n, N)) |- heightFunApplicationDef
    ) by Weakening
    thenHave(
      (isHeight(h), in(n, N)) |-
        in(n, N) ==> forall(x, in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM)
    ) by InstantiateForall(n)
    thenHave(
      (isHeight(h), in(n, N)) |-
        forall(x, in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM)
    ) by Restate
    thenHave(
      (isHeight(h), in(n, N)) |-
        in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM
    ) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }

  /**
   *  Lemma --- The height function is monotonic
   *
   *  `n <= m => height(n) ⊆ height(m)`
   *
   *  TODO: Try to pull out
   */
  private[encoding] val heightMonotonic = Lemma(
    (isHeight(h), in(n, N), subset(m, n)) |- subset(app(h, m), app(h, n))
  ) {

    // STEP 0: Caching
    val extendedIntroFunRestrictedFunM =
      isInExtendedIntroductionFunctionImage(restrictedFunction(h, m))(x)
    val extendedIntroFunRestrictedFunN =
      isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)

    // STEP 1: Unfold the definition of height(m)
    have((n ∈ N, m ⊆ n) |- m ∈ N) by Tautology.from(subsetIsNat of (x := m, y := n))
    have(
      (isHeight(h), n ∈ N, m ⊆ n) |- (x ∈ app(h, m)) <=>
        extendedIntroFunRestrictedFunM
    ) by Cut(lastStep, heightApplication of (n := m))

    val unfoldHeightApplicationM = have(
      (isHeight(h), in(n, N), subset(m, n), in(x, app(h, m))) |-
        extendedIntroFunRestrictedFunM
    ) by Cut(
      lastStep,
      equivalenceRevApply of
        (p1 := in(x, app(h, m)), p2 := extendedIntroFunRestrictedFunM)
    )

    // STEP 2: Use the monotonicity of the extended introduction function
    have(
      subset(m, n) |-
        extendedIntroFunRestrictedFunM ==>
        extendedIntroFunRestrictedFunN
    ) by Cut(
      restrictedFunctionDomainMonotonic of (x := m, y := n, f := h),
      extendedIntroductionFunctionMonotonic of
        (f := restrictedFunction(h, m), g := restrictedFunction(h, n))
    )
    val extNFromMonotonic = have(
      (isHeight(h), in(n, N), subset(m, n), extendedIntroFunRestrictedFunM) |-
        extendedIntroFunRestrictedFunN
    ) by Tautology.from(lastStep)

    val inHnFromExtended = have(
      (isHeight(h), in(n, N), extendedIntroFunRestrictedFunN) |-
        in(x, app(h, n))
    ) by Cut(
      heightApplication of (n := n),
      equivalenceRevApply of
        (p1 := extendedIntroFunRestrictedFunN, p2 := in(x, app(h, n)))
    )

    have(
      (isHeight(h), in(n, N), subset(m, n), extendedIntroFunRestrictedFunM) |-
        in(x, app(h, n))
    ) by Cut(extNFromMonotonic, inHnFromExtended)

    // STEP 3: Fold the definition of subset
    have(
      (isHeight(h), in(n, N), subset(m, n), in(x, app(h, m))) |- in(x, app(h, n))
    ) by Cut(unfoldHeightApplicationM, lastStep)
    thenHave(
      (isHeight(h), in(n, N), subset(m, n)) |-
        in(x, app(h, m)) ==> in(x, app(h, n))
    ) by RightImplies
    thenHave(
      (isHeight(h), in(n, N), subset(m, n)) |-
        forall(x, in(x, app(h, m)) ==> in(x, app(h, n)))
    ) by RightForall

    have(thesis) by Tautology.from(
      subsetAxiom of (x := app(h, m), y := app(h, n)),
      equivalenceRevApply of (
          p1 := forall(x, in(x, app(h, m)) ==> in(x, app(h, n))),
          p2 := subset(app(h, m), app(h, n))
      ), lastStep
    )
  }

  /**
   *  Lemma --- There is no element of height 0 in the ADT.
   *
   *  `!∃x ∈ adt. height(x) = 0`
   */
  private[encoding] val heightZero = Lemma(isHeight(h) |- !in(x, app(h, ∅))) {

    // This is due to the fact that the extended introduction function is the empty set when the function is empty
    // (which happens when the height is set to 0).
    have(
      isHeight(h) |-
        in(x, app(h, ∅)) <=>
        isInExtendedIntroductionFunctionImage(restrictedFunction(h, ∅))(x)
    ) by Cut(zeroIsNat, heightApplication of (n := ∅))
    thenHave(
      (restrictedFunction(h, ∅) === ∅, isHeight(h)) |- !in(x, app(h, ∅))
    ) by RightSubstEq.withParameters(
      List((restrictedFunction(h, ∅), ∅)),
      (Seq(s), in(x, app(h, ∅)) <=> isInExtendedIntroductionFunctionImage(s)(x))
    )
    have(thesis) by Cut(restrictedFunctionEmptyDomain, lastStep)
  }

  /**
   *  Lemma --- The set of elements of height n + 1 is the set of elements of height n to
   *  which the introduction function is applied.
   *
   *  `height(n + 1) = introductionFunction(height(n))`
   */
  private[encoding] val heightSuccessorWeak = Lemma(
    (isHeight(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)
  ) {

    // STEP 1: Prove that the restriction of height to n + 1 is not empty
    val restrHeightNotEmpty: Expr[Prop] = !(restrictedFunction(h, successor(n)) === ∅)
    have(!(h === ∅) |- restrHeightNotEmpty) by
      Cut(zeroIsNotSucc, restrictedFunctionNotEmpty of (d := successor(n)))
    val restrHeightNotEmptyLemma = have(isHeight(h) |- restrHeightNotEmpty) by
      Cut(heightFunctionNonEmpty, lastStep)

    // STEP 2: Use the fact that if the function is cumulative then ∪ range(height | n + 1) = height(n) to conclude the proof
    have(
      (isHeight(h), in(n, N)) |- subset(m, n) ==> subset(app(h, m), app(h, n))
    ) by RightImplies(heightMonotonic)
    thenHave(
      (isHeight(h), in(n, N)) |-
        forall(m, subset(m, n) ==> subset(app(h, m), app(h, n)))
    ) by RightForall
    val unionRangeRestr = have(
      (isHeight(h), in(n, N)) |-
        unionRange(restrictedFunction(h, successor(n))) === app(h, n)
    ) by Sorry //Tautology.from(lastStep, unionRangeCumulativeRestrictedFunction)
    // TODO: update unionRangeCumulativeRestrictedFunction with isHeight(h)

    val succIsNatStep = have((isHeight(h), in(n, N)) |- in(successor(n), N)) by
      Tautology.from(successorIsNat)

    have(
      (isHeight(h), in(n, N)) |-
        in(x, app(h, successor(n))) <=>
        isInExtendedIntroductionFunctionImage(restrictedFunction(h, successor(n)))(x)
    ) by Cut(
      succIsNatStep,
      heightApplication of (n := successor(n))
    )

    thenHave(
      (
        isHeight(h),
        in(n, N),
        unionRange(restrictedFunction(h, successor(n))) === app(h, n)
      ) |-
        in(x, app(h, successor(n))) <=>
        restrHeightNotEmpty /\ isInIntroductionFunctionImage(app(h, n))(x)
    ) by RightSubstEq.withParameters(
      List((unionRange(restrictedFunction(h, successor(n))), app(h, n))),
      (
        Seq(s),
        in(x, app(h, successor(n))) <=>
          (restrHeightNotEmpty /\ isInIntroductionFunctionImage(s)(x))
      )
    )

    have(
      (isHeight(h), in(n, N)) |- 
      in(x, app(h, successor(n))) <=> restrHeightNotEmpty /\ isInIntroductionFunctionImage(app(h, n))(x)
    ) by Cut(unionRangeRestr, lastStep)

    have(
      (isHeight(h), in(n, N), restrHeightNotEmpty) |-
        in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)
    ) by Cut(lastStep, equivalenceAnd of (
      p1 := in(x, app(h, successor(n))),
      p2 := restrHeightNotEmpty,
      p3 := isInIntroductionFunctionImage(app(h, n))(x)
    ))

    have(thesis) by Cut(restrHeightNotEmptyLemma, lastStep)
  }
}
