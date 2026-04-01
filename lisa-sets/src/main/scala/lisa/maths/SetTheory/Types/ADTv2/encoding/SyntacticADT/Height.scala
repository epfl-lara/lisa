package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.UnionRangeCollapse.unionRangeCollapse

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

private[encoding] trait SyntacticADTHeight[N <: Arity]
    extends SyntacticADTIntroduction[N] {
  this: SyntacticADT[N] =>

  /** Non-polymorphic body of isHeight, before quantification over type variables. */
  private[encoding] def isHeightCore(hh: Expr[Ind]): Expr[Prop] =
    function(hh) /\
      (dom(hh) === N) /\
      forall(
        n,
        in(n, N) ==> forall(
          x,
          in(x, app(hh, n)) <=>
            inExtIntroImage(restrictedFunction(hh, n))(x)
        )
      )

  /** Unfold isHeight(h) and instantiate all quantified type variables. */
  private[encoding] def unfoldIsHeight(using
      lib: lisa.utils.prooflib.Library,
      proof: lib.Proof
  ): proof.Fact = {
    val coreAll = forallSeq(typeVariables, isHeightCore(h))
    val withAllTypes = lib.have(isHeight(h) |- coreAll) by
      Tautology.from(isHeight.definition)
    lib.have(isHeight(h) |- isHeightCore(h)) by
      InstantiateForall(typeVariables*)(withAllTypes)
  }

  // *******************
  // * HEIGHT FUNCTION *
  // *******************

  /**
   *  Lemma --- The extended introduction function is monotonic with respect to set
   *  inclusion.
   *
   *  `f ⊆ g |- extendedIntroductionFunction(f) ⊆ extendedIntroductionFunction(g)`
   */
  private[encoding] val extIntroMonotonic = Lemma(
    subset(f, g) |-
      inExtIntroImage(f)(x) ==>
      inExtIntroImage(g)(x)
  ) {

    // STEP 0: Caching
    val introUnionF = inIntroImage(unionRange(f))(x)
    val introUnionG = inIntroImage(unionRange(g))(x)

    // STEP 1: Instantiate monotonicity of the introduction function for the union of the ranges of f and g
    have(subset(f, g) |- introUnionF ==> introUnionG) by Cut(
      unionRangeMonotonic,
      introductionFunctionMononotic of (s := unionRange(f), t := unionRange(g))
    )
    val left = thenHave((subset(f, g), introUnionF) |- introUnionG) by
      Restate

    // STEP 2: Conclude by applying the conjuction on both sides
    have(
      (subset(f, g), !(f === ∅), introUnionF) |-
        inExtIntroImage(g)(x)
    ) by RightAnd(left, subsetNotEmpty of (x := f, y := g))
  }

  /**
   *  Lemma --- There exists a unique height function for this ADT.
   *
   *  `∃!h. h = height`
   *
   *  TODO: Prove this using transfinite recursion
   */
  private[encoding] val heightFunUnique = Axiom(existsOne(h, isHeight(h)))

  /**
   *  Lemma --- The height function exists.
   *
   *  `∃h. h = height`
   */
  private[encoding] val heightExists = Lemma(exists(h, isHeight(h))) {
    have(thesis) by Cut(
      heightFunUnique.asInstanceOf,
      lisa.maths.Quantifiers.existsOneImpliesExists of
        (P := lam(h, isHeight(h)))
    )
  }

  /**
   *  Lemma --- If two functions are the height function then they are the same.
   *
   *  `f = height /\ h = height => f = h`
   */
  private[encoding] val heightFunUniqueEq =
    Lemma((isHeight(f), isHeight(h)) |- f === h) {
      have(thesis) by Cut(
        heightFunUnique,
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
      val heightDomEqN = have(isHeight(h) |- dom(h) === N) by
        Tautology.from(unfoldIsHeight)
      val domRefl = have(dom(h) === dom(h)) by Congruence

      have(N === ∅ |- ()) by Restate.from(natNotEmpty)
      thenHave(
        (
          dom(h) === ∅,
          dom(h) === N,
          dom(h) === dom(h)
        ) |- ()
      ) by LeftSubstEq.withParameters(
        List((dom(h), ∅), (dom(h), N)),
        (Seq(x, y), y === x)
      )
      // thenHave(
      //   (dom(h) === N, dom(h) === dom(h)) |-
      //     !(dom(h) === ∅)
      // ) by Tautology
      have(
        (
          isHeight(h),
          dom(h) === ∅,
          dom(h) === dom(h)
        ) |- ()
      ) by Cut(heightDomEqN, lastStep)
      thenHave(
        (isHeight(h), dom(h) === dom(h)) |-
          !(dom(h) === ∅)
      ) by RightNot
      have(isHeight(h) |- !(dom(h) === ∅)) by Cut(domRefl, lastStep)
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
      inExtIntroImage(restrictedFunction(h, n))(x)
  ) {

    // Caching
    val extIntroResM =
      inExtIntroImage(restrictedFunction(h, n))(x)
    val heightFunApplicationDef = forall(
      n,
      in(n, N) ==> forall(x, in(x, app(h, n)) <=> extIntroResM)
    )

    // Unfold the dedicated height-function predicate and instantiate the specification.
    have(isHeight(h) |- heightFunApplicationDef) by
      Tautology.from(unfoldIsHeight)
    thenHave(
      (isHeight(h), in(n, N)) |- heightFunApplicationDef
    ) by Weakening
    thenHave(
      (isHeight(h), in(n, N)) |-
        in(n, N) ==> forall(x, in(x, app(h, n)) <=> extIntroResM)
    ) by InstantiateForall(n)
    thenHave(
      (isHeight(h), in(n, N)) |-
        forall(x, in(x, app(h, n)) <=> extIntroResM)
    ) by Restate
    thenHave(
      (isHeight(h), in(n, N)) |-
        in(x, app(h, n)) <=> extIntroResM
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
    val extIntroResM =
      inExtIntroImage(restrictedFunction(h, m))(x)
    val extIntroResN =
      inExtIntroImage(restrictedFunction(h, n))(x)

    // STEP 1: Unfold the definition of height(m)
    have((n ∈ N, m ⊆ n) |- m ∈ N) by Tautology.from(subsetIsNat of (x := m, y := n))
    have(
      (isHeight(h), n ∈ N, m ⊆ n) |- (x ∈ app(h, m)) <=>
        extIntroResM
    ) by Cut(lastStep, heightApplication of (n := m))

    val unfoldHeightApplicationM = have(
      (isHeight(h), in(n, N), subset(m, n), in(x, app(h, m))) |-
        extIntroResM
    ) by Cut(
      lastStep,
      equivalenceRevApply of
        (p1 := in(x, app(h, m)), p2 := extIntroResM)
    )

    // STEP 2: Use the monotonicity of the extended introduction function
    have(
      subset(m, n) |-
        extIntroResM ==>
        extIntroResN
    ) by Cut(
      restrictedFunctionDomainMonotonic of (x := m, y := n, f := h),
      extIntroMonotonic of
        (f := restrictedFunction(h, m), g := restrictedFunction(h, n))
    )
    val extNFromMonotonic = have(
      (isHeight(h), in(n, N), subset(m, n), extIntroResM) |-
        extIntroResN
    ) by Tautology.from(lastStep)

    val inHnFromExtended = have(
      (isHeight(h), in(n, N), extIntroResN) |-
        in(x, app(h, n))
    ) by Cut(
      heightApplication of (n := n),
      equivalenceRevApply of
        (p1 := extIntroResN, p2 := in(x, app(h, n)))
    )

    have(
      (isHeight(h), in(n, N), subset(m, n), extIntroResM) |-
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
        inExtIntroImage(restrictedFunction(h, ∅))(x)
    ) by Cut(zeroIsNat, heightApplication of (n := ∅))
    thenHave(
      (restrictedFunction(h, ∅) === ∅, isHeight(h)) |- !in(x, app(h, ∅))
    ) by RightSubstEq.withParameters(
      List((restrictedFunction(h, ∅), ∅)),
      (Seq(s), in(x, app(h, ∅)) <=> inExtIntroImage(s)(x))
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
      in(x, app(h, successor(n))) <=> inIntroImage(app(h, n))(x)
  ) {

    // STEP 1: Prove that the restriction of height to n + 1 is not empty
    val heightResNonEmpty: Expr[Prop] = !(restrictedFunction(h, successor(n)) === ∅)
    have(!(h === ∅) |- heightResNonEmpty) by
      Cut(zeroIsNotSucc, restrictedFunctionNotEmpty of (d := successor(n)))
    val heightResNonEmptyLemma = have(isHeight(h) |- heightResNonEmpty) by
      Cut(heightFunctionNonEmpty, lastStep)

    // STEP 2: Use the fact that if the function is cumulative then ∪ range(height | n + 1) = height(n) to conclude the proof
    have(
      (isHeight(h), in(n, N)) |- subset(m, n) ==> subset(app(h, m), app(h, n))
    ) by RightImplies(heightMonotonic)
    val monotonicityForall = thenHave(
      (isHeight(h), in(n, N)) |-
        forall(m, subset(m, n) ==> subset(app(h, m), app(h, n)))
    ) by RightForall

    val coreTyping = have(
      (isHeight(h), in(n, N)) |- function(h) /\ (dom(h) === N)
    ) by Tautology.from(unfoldIsHeight)
    val nInNFact = have((isHeight(h), in(n, N)) |- in(n, N)) by Hypothesis
    val coreTypingAndN = have(
      (isHeight(h), in(n, N)) |- (function(h) /\ (dom(h) === N)) /\ in(n, N)
    ) by RightAnd(coreTyping, nInNFact)

    have(
      (isHeight(h), in(n, N)) |- (
        function(h) /\
        (dom(h) === N) /\
        in(n, N) /\
        forall(m, subset(m, n) ==> subset(app(h, m), app(h, n)))
      )
    ) by RightAnd(coreTypingAndN, monotonicityForall)

    val unionRangeRes = have(
      (isHeight(h), in(n, N)) |-
        unionRange(restrictedFunction(h, successor(n))) === app(h, n)
    ) by Tautology.from(lastStep, unionRangeCollapse)

    val succIsNatStep = have((isHeight(h), in(n, N)) |- in(successor(n), N)) by
      Tautology.from(successorIsNat)

    have(
      (isHeight(h), in(n, N)) |-
        in(x, app(h, successor(n))) <=>
        inExtIntroImage(restrictedFunction(h, successor(n)))(x)
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
        heightResNonEmpty /\ inIntroImage(app(h, n))(x)
    ) by RightSubstEq.withParameters(
      List((unionRange(restrictedFunction(h, successor(n))), app(h, n))),
      (
        Seq(s),
        in(x, app(h, successor(n))) <=>
          (heightResNonEmpty /\ inIntroImage(s)(x))
      )
    )

    have(
      (isHeight(h), in(n, N)) |- 
      in(x, app(h, successor(n))) <=> heightResNonEmpty /\ inIntroImage(app(h, n))(x)
    ) by Cut(unionRangeRes, lastStep)

    have(
      (isHeight(h), in(n, N), heightResNonEmpty) |-
        in(x, app(h, successor(n))) <=> inIntroImage(app(h, n))(x)
    ) by Cut(lastStep, equivalenceAnd of (
      p1 := in(x, app(h, successor(n))),
      p2 := heightResNonEmpty,
      p3 := inIntroImage(app(h, n))(x)
    ))

    have(thesis) by Cut(heightResNonEmptyLemma, lastStep)
  }
}
