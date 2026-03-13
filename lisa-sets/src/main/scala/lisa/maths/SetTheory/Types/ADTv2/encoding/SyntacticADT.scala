package lisa.maths.SetTheory.Types.ADTv2.transation

import lisa.maths.SetTheory.Types.ADTv2
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.transation.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*
import lisa.automation.Substitution.Apply

type **[A, N <: Arity] = Tuple

/**
 *  Syntactic set theoretical interpretation of an algebraic data type. That is the least
 *  set closed under [[SyntacticConstructor]].
 *
 *  E.g. list is the smallest set containing nil and closed under the syntactic operation
 *  cons.
 *
 *  Injectivity between different constructors, introduction rules and structural
 *  induction are proved within this class.
 *
 *  @constructor creates a new algebraic data type out of a user specification.
 *  @param line the line at which the ADT is defined. Usually fetched automatically by the
 *    compiler. Used for error reporting
 *  @param file the file in which the ADT is defined. Usually fetched automatically by the
 *    compiler. Used for error reporting
 *  @param name the name of the ADT
 *  @param constructors constructors of the ADT
 *  @param typeVariables type variables used in the definition of this ADT
 */
class SyntacticADT[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
    val name: String,
    val constructors: Seq[SyntacticConstructor],
    val typeVariables: Variable[Ind] ** N
) {

  /** Sequence of type variables used in the definition of this ADT */
  val typeVariablesSeq: Seq[Variable[Ind]] = typeVariables.toSeq @@

  /** Number of type variables used in the definition of this ADT */
  val typeArity: N = typeVariablesSeq.length.asInstanceOf[N]

  // ***************
  // * INJECTIVITY *
  // ***************

  /**
   *  Theorem --- Injectivity of constructors.
   *
   *  Two instances of different construcors are always different.
   *
   *  e.g. Nil != Cons(head, tail)
   */
  def injectivity(c1: SyntacticConstructor, c2: SyntacticConstructor) =
    require(c1.tag != c2.tag, "The given constructors must be different.")

    Lemma(!(c1.term1 === c2.term2)) {

      // STEP 0: Caching
      val tagTerm1: Expr[Ind] = c1.tagTerm
      val tagTerm2: Expr[Ind] = c2.tagTerm

      // STEP 1: Prove that the tags are different
      val diffTag = have(!(tagTerm1 === tagTerm2)) subproof {

        // STEP 1.1: Order the tags
        val minTag: Int = Math.min(c1.tag, c2.tag)
        val maxTag: Int = Math.max(c1.tag, c2.tag)

        val start =
          have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Restate

        // STEP 1.2: Apply successor injectivity to both tags until one becomes 0
        (1 to minTag).foldLeft(start)((fact, i) =>
          val midMaxTag = toTerm(maxTag - i)
          val midMinTag = toTerm(minTag - i)
          have(
            successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag
          ) by Cut(
            ADTThm.successorInjectivity of (n := midMaxTag, m := midMinTag),
            ADTThm.equivalenceApply of (
              p1 := successor(midMaxTag) === successor(midMinTag),
              p2 := midMaxTag === midMinTag
            )
          )
          have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
        )

        val chainInjectivity = thenHave(
          !(toTerm(maxTag - minTag) === ∅) |- !(tagTerm1 === tagTerm2)
        ) by Restate

        // STEP 1.3: Conclude using the fact that 0 is not the successor of any number
        have(!(toTerm(maxTag - minTag) === ∅)) by Exact(ADTThm.zeroIsNotSucc)
        have(thesis) by Cut(lastStep, chainInjectivity)
      }

      // STEP 2: Prove that the terms are different if the tags are different
      have(
        c1.term1 === c2.term2 |- (tagTerm1 === tagTerm2) /\ (c1.subterm1 === c2.subterm2)
      ) by Apply(ADTThm.equivalenceRevApply).on(
        Pair.extensionality of (
          a := tagTerm1,
          b := c1.subterm1,
          c := tagTerm2,
          d := c2.subterm2
        )
      )
      thenHave(!(tagTerm1 === tagTerm2) |- !(c1.term1 === c2.term2)) by Weakening

      // STEP 3: Conclude
      have(!(c1.term1 === c2.term2)) by Cut(diffTag, lastStep)
    }

  // *************************
  // * INTRODUCTION FUNCTION *
  // *************************

  /**
   *  Formula describing whether the variables of a constructor belongs to their
   *  respective domain or s when they are self-referencing.
   *
   *  @param c The considered constructor
   *  @param s The set of elements in which self-referencing variables of the constructor
   *    are.
   */
  private def constructorVarsInDomain(c: SyntacticConstructor, s: Expr[Ind]): Expr[Prop] =
    wellTypedFormula(c.signature)(s)

  /**
   *  Formula describing whether an element x is an instance of a specific constructor.
   *
   *  @param c The constructor we want to check if x is an instance of
   *  @param x The element we want to check if it is an instance of c
   *  @param s The set of elements in which self-referencing arguments of the constructor
   *    are.
   */
  private def isConstructor(
      c: SyntacticConstructor,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables2, wellTypedFormula(c.signature2)(s) /\ (x === c.term2))

  /**
   *  Formula describing whether an element x is an instance of one of this ADT's
   *  constructors.
   *
   *  @param x The element we want to check if it is an instance of some constructor.
   *  @param s The set of elements in which self-referencing arguments of the constructor
   *    are.
   */
  private def isConstructor(x: Expr[Ind], s: Expr[Ind]): Expr[Prop] = Utils
    .\/(constructors.map(c => isConstructor(c, x, s)))

  /**
   *  The introduction (class) function applies this ADT's constructors to the argument to
   *  given to it. It then adds to elements of the resulting set to the one given in
   *  argument. For example, if all arguments of the constructors were self-referencing we
   *  would have:
   *
   *  introductionFunction(s) = {y | y = c(x1, ..., xn) for some c ∈ constructors and x1,
   *  ..., xn ∈ s} ∪ s
   *
   *  In order to avoid introducing a new symbol in the theory, we describe this function
   *  with a predicate.
   *
   *  @param s the argument of this function, i.e. set of elements on which the
   *    constructors are applied
   *  @param y the element we want to check if it is in the image of s under the
   *    introduction function.
   *
   *  @return a formula describing whether y ∈ introductionFunction(s)
   *
   *  @note The existence of the image of the introduction function is guaranteed by the
   *    union and replacement axioms. Moreover, it is not necessary to compute the union
   *    with s. It however simplifies further proofs. See [[this.heightSuccessorStrong]]
   *    for a proof of the equivalence of the two definitions.
   */
  private def isInIntroductionFunctionImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    isConstructor(y, s) \/ in(y, s)

  /**
   *  Lemma --- The introduction function is monotonic with respect to set inclusion.
   *
   *  `s ⊆ t |- introductionFunction(s) ⊆ introductionFunction(t)`
   */
  private val introductionFunctionMononotic = Lemma(
    subset(s, t) |- isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(
      t
    )(x)
  ) {
    // In the rest of the proof we assume that s ⊆ t

    // STEP 0: Caching predicates that are often used
    val subsetST = subset(s, t)
    val isConstructorXS = isConstructor(x, s)
    val isConstructorXT = isConstructor(x, t)

    // STEP 1: Prove x ∈ s implies x ∈ t
    have(subsetST |- forall(z, in(z, s) ==> in(z, t))) by Apply(
      ADTThm.equivalenceApply of (p1 := subsetST)
    ).on(subsetAxiom.asInstanceOf)
    val subsetElimination =
      thenHave(subsetST |- in(z, s) ==> in(z, t)) by InstantiateForall(z)

    // STEP 2: For each constructor, prove that if x is an instance of that constructor with self referencing arguments in s
    // then it is also an instance of some constructor with self referencing arguments in t
    val isConstructorXSImpliesT =
      for c <- constructors yield
        // STEP 2.0: Caching predicates that are often used
        // TODO change identifier
        val labelEq = x === c.term2
        val isConstructorCXS = isConstructor(c, x, s)
        val isConstructorCXT = isConstructor(c, x, t)
        val varsWellTypedS = wellTypedFormula(c.signature2)(s)
        val varsWellTypedT = wellTypedFormula(c.signature2)(t)

        if c.arity == 0 then
          have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
        else
          // STEP 2.1: Prove that we can expand the domain of the (quantified) variables of the constructor
          val andSeq =
            for (v, ty) <- c.signature2
            yield have((subsetST, varsWellTypedS) |- in(v, ty.getOrElse(t))) by Weakening(
              subsetElimination of (z := v)
            )
          val expandingDomain =
            have((subsetST, varsWellTypedS) |- varsWellTypedT) by RightAnd(andSeq*)
          val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
          have(
            (subsetST, varsWellTypedS, labelEq) |- varsWellTypedT /\ labelEq
          ) by RightAnd(expandingDomain, weakeningLabelEq)

          // STEP 2.2: Prove that x stays an instance of this constructor if we expand the domain of the variables
          thenHave(
            (subsetST, varsWellTypedS, labelEq) |- isConstructorCXT
          ) by QuantifiersIntro(c.variables2)
          thenHave((subsetST, varsWellTypedS /\ labelEq) |- isConstructorCXT) by LeftAnd
          thenHave((subsetST, isConstructorCXS) |- isConstructorCXT) by QuantifiersIntro(
            c.variables2
          )

          // STEP 2.3: Weaken the conclusion to some constructor instead of a specific one
          thenHave((subsetST, isConstructorCXS) |- isConstructorXT) by Weakening

    // STEP 3: Prove that this holds for any constructor
    // ? Steps 2 and 3 can be merged and optimized through the repeated use of an external theorem like [[ADTHelperTheorems.unionPreimageMonotonic]]
    if constructors.isEmpty then
      have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
    else
      have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(
        isConstructorXSImpliesT*
      )

    // STEP 4: Prove the thesis by showing that making the union with the function argument does not change the monotonicity
    thenHave(subsetST |- isConstructorXS ==> isConstructorXT) by RightImplies
    have(thesis) by Cut(
      lastStep,
      ADTThm.unionPreimageMonotonic of (P := lambda(s, isConstructorXS))
    )
  }

  /**
   *  Lemma --- Every constructor is in the image of the introduction function.
   *
   *  `For every c ∈ constructors, xi ∈ s, ..., xj ∈ s |- c(x1, ..., xn) ∈ introductionFunction(s)`
   */
  private val constructorIsInIntroductionFunction = constructors.map(c =>
    // Caching
    val constructorVarsInDomainCS = constructorVarsInDomain(c, s)

    c -> Lemma(constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)) {

      have(
        constructorVarsInDomainCS |- constructorVarsInDomainCS /\ (c.term === c.term)
      ) by Restate

      // Replace each variable on the LHS of the equality by a quantified variable and then introduce an existential quantifier
      c.variables2.foldRight((c.variables1, List[Variable[Ind]]()))((v, acc) =>

        // At each step remove a variable and add a quantified one
        val oldVariables = acc._1.init
        val newVariables = v :: acc._2
        val vars = oldVariables ++ newVariables

        thenHave(
          constructorVarsInDomainCS |- existsSeq(
            newVariables,
            wellTypedFormula(vars.zip(c.specification))(s) /\ (c.term(vars) === c.term)
          )
        ) by RightExists

        (oldVariables, newVariables)
      )

      thenHave(
        constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)
      ) by Weakening
    }
  ).toMap

  // **********************************
  // * EXTENDED INTRODUCTION FUNCTION *
  // **********************************

  /**
   *  The extended introduction (class) function takes a function f as an argument instead
   *  of set.
   *    - If f is not empty, it calls the introduction function on the union of the ranges
   *      of the function. Since f will always be cumulative by assumption, this is
   *      equivalent as passing as argument the broadest set among the ranges of f.
   *    - If the function is empty, it returns the empty set.
   *
   *  This class function is in a suited format to be used within the transfinite
   *  recursion theorem, which will be called to construct the height function.
   *
   *  @see [[this.heightFunctionUniqueness]]
   *
   *  @param f the function given as argument to the extended introduction function
   *  @param x the element we want to check if it is in the image of f under the extended
   *    introduction function
   *  @return a formula describing whether x ∈ extendedIntroductionFunction(f)
   */
  private def isInExtendedIntroductionFunctionImage(f: Expr[Ind])(
      x: Expr[Ind]
  ): Expr[Prop] = !(f === ∅) /\ isInIntroductionFunctionImage(unionRange(f))(x)

  /**
   *  Lemma --- The extended introduction function is monotonic with respect to set
   *  inclusion.
   *
   *  `f ⊆ g |- extendedIntroductionFunction(f) ⊆ extendedIntroductionFunction(g)`
   */
  private val extendedIntroductionFunctionMonotonic = Lemma(
    subset(f, g) |- isInExtendedIntroductionFunctionImage(f)(
      x
    ) ==> isInExtendedIntroductionFunctionImage(g)(x)
  ) {

    // STEP 0: Caching
    val introFunUnionRangeF = isInIntroductionFunctionImage(unionRange(f))(x)
    val introFunUnionRangeG = isInIntroductionFunctionImage(unionRange(g))(x)

    // STEP 1: Instantiate monotonicity of the introduction function for the union of the ranges of f and g
    have(subset(f, g) |- introFunUnionRangeF ==> introFunUnionRangeG) by Cut(
      ADTThm.unionRangeMonotonic,
      introductionFunctionMononotic of (s := unionRange(f), t := unionRange(g))
    )
    val left =
      thenHave((subset(f, g), introFunUnionRangeF) |- introFunUnionRangeG) by Restate

    // STEP 2: Conclude by applying the conjuction on both sides
    have(
      (
        subset(f, g),
        !(f === ∅),
        introFunUnionRangeF
      ) |- isInExtendedIntroductionFunctionImage(g)(x)
    ) by RightAnd(left, ADTThm.subsetNotEmpty of (x := f, y := g))
  }

  // *******************
  // * HEIGHT FUNCTION *
  // *******************

  /**
   *  The height function assigns to each natural number the set of elements of the ADT of
   *  that height or below. The set of terms with height 0 is empty. Non inductive
   *  constructors have height one. The height of an instance of an inductive constructor
   *  is the maximum height of its arguments plus one. The height function is guaranteed
   *  to exists and is unique.
   *
   *  @see [[this.heightFunctionUniqueness]]
   *
   *  @param g the function we want to know if it is the height function
   *
   *  @return a formula that is true if and only if g is the height function
   */
  private def isTheHeightFunction(h: Expr[Ind]): Expr[Prop] =
    functional(h) /\ (relationDomain(h) === N) /\ forall(
      n,
      in(n, N) ==> forall(
        x,
        in(x, app(h, n)) <=> isInExtendedIntroductionFunctionImage(
          restrictedFunction(h, n)
        )(x)
      )
    )

  // Caching
  private val fIsTheHeightFunction: Expr[Prop] = isTheHeightFunction(f)
  private val hIsTheHeightFunction: Expr[Prop] = isTheHeightFunction(h)

  /**
   *  Lemma --- There exists a unique height function for this ADT.
   *
   *  `∃!h. h = height`
   *
   *  TODO: Prove this using transfinite recursion
   */
  private val heightFunUniqueness = Axiom(existsOne(h, hIsTheHeightFunction))

  /**
   *  Lemma --- The height function exists.
   *
   *  `∃h. h = height`
   */
  private val heightFunctionExistence = Lemma(exists(h, hIsTheHeightFunction)) {
    have(thesis) by Apply(
      lisa.maths.Quantifiers.existsOneImpliesExists of (
        P := lambda(h, hIsTheHeightFunction)
      )
    ).on(heightFunUniqueness.asInstanceOf)
  }

  /**
   *  Lemma --- If two functions are the height function then they are the same.
   *
   *  `f = height /\ h = height => f = h`
   */
  private val heightFunctionUniqueness2 =
    Lemma((fIsTheHeightFunction, hIsTheHeightFunction) |- f === h) {
      have(thesis) by Cut(
        heightFunUniqueness,
        ADTThm.existsOneUniqueness of (
          P := lambda(h, hIsTheHeightFunction),
          x := f,
          y := h
        )
      )
    }

  /**
   *  Lemma --- The height function is not empty.
   *
   *  `height ≠ ∅`
   */
  private val heightFunctionNonEmpty = Lemma(hIsTheHeightFunction |- !(h === ∅)) {
    // The proof goes by contradiction. If the height function is empty then its domain is empty as well.
    // This would imply that the set of natural numbers is empty, which is a contradiction.
    have(N === ∅ |- ()) by Restate.from(ADTThm.natNotEmpty)
    thenHave(
      (
        relationDomain(h) === ∅,
        relationDomain(h) === N,
        relationDomain(h) === relationDomain(h)
      ) |- ()
    ) by LeftSubstEq.withParametersSimple(
      List((relationDomain(h), ∅), (relationDomain(h), N)),
      lambda((x, y), y === x)
    )
    thenHave(
      (relationDomain(h) === N, relationDomain(h) === relationDomain(h)) |- !(
        relationDomain(h) === ∅
      )
    ) by RightNot
    have(thesis) by Apply(ADTThm.nonEmptyDomain).on(lastStep)
  }

  /**
   *  Lemma --- The set of elements of height n or below is the image of the extended
   *  introduction function under the height function restricted to n (consequence of
   *  transfinite recursion).
   *
   *  `height(n) = extendedIntroductionFunction(height | n)`
   */
  private val heightApplication = Lemma(
    (hIsTheHeightFunction, in(n, N)) |- in(
      x,
      app(h, n)
    ) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)
  ) {

    // Caching
    val extendedIntroFunRestrictedFunM =
      isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)
    val heightFunApplicationDef = forall(
      n,
      in(n, N) ==> forall(x, in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM)
    )

    // Nothing fancy, just instantiations and restates
    have(heightFunApplicationDef |- heightFunApplicationDef) by Hypothesis
    thenHave(
      heightFunApplicationDef |- in(n, N) ==> forall(
        x,
        in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM
      )
    ) by InstantiateForall(n)
    thenHave(
      (heightFunApplicationDef, in(n, N)) |- forall(
        x,
        in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM
      )
    ) by Restate
    thenHave(
      (heightFunApplicationDef, in(n, N)) |- in(
        x,
        app(h, n)
      ) <=> extendedIntroFunRestrictedFunM
    ) by InstantiateForall(x)
    thenHave(thesis) by Weakening
  }

  /**
   *  Lemma --- The height function is monotonic
   *
   *  `n <= m => height(n) ⊆ height(m)`
   *
   *  TODO: Try to pull out
   */
  private val heightMonotonic = Lemma(
    (hIsTheHeightFunction, in(n, N), subset(m, n)) |- subset(app(h, m), app(h, n))
  ) {

    // STEP 0: Caching
    val extendedIntroFunRestrictedFunM =
      isInExtendedIntroductionFunctionImage(restrictedFunction(h, m))(x)

    // STEP 1: Unfold the definition of height(m)
    have(
      (hIsTheHeightFunction, in(n, N), subset(m, n)) |- in(
        x,
        app(h, m)
      ) <=> extendedIntroFunRestrictedFunM
    ) by Apply(heightApplication).on(ADTThm.subsetIsNat.asInstanceOf)
    val unfoldHeightApplicationM = have(
      (
        hIsTheHeightFunction,
        in(n, N),
        subset(m, n),
        in(x, app(h, m))
      ) |- extendedIntroFunRestrictedFunM
    ) by Cut(
      lastStep,
      ADTThm.equivalenceRevApply of (
        p1 := in(x, app(h, m)),
        p2 := extendedIntroFunRestrictedFunM
      )
    )

    // STEP 2: Use the monotonicity of the extended introduction function
    have(
      subset(
        m,
        n
      ) |- extendedIntroFunRestrictedFunM ==> isInExtendedIntroductionFunctionImage(
        restrictedFunction(h, n)
      )(x)
    ) by Cut(
      ADTThm.restrictedFunctionDomainMonotonic of (x := m, y := n, f := h),
      extendedIntroductionFunctionMonotonic of (
        f := restrictedFunction(h, m),
        g := restrictedFunction(h, n)
      )
    )
    have(
      (
        hIsTheHeightFunction,
        in(n, N),
        subset(m, n),
        extendedIntroFunRestrictedFunM
      ) |- in(x, app(h, n))
    ) by Apply(ADTThm.equivalenceRevApply).on(lastStep, heightApplication.asInstanceOf)

    // STEP 3: Fold the definition of subset
    have(
      (hIsTheHeightFunction, in(n, N), subset(m, n), in(x, app(h, m))) |- in(x, app(h, n))
    ) by Cut(unfoldHeightApplicationM, lastStep)
    thenHave(
      (hIsTheHeightFunction, in(n, N), subset(m, n)) |- in(x, app(h, m)) ==> in(
        x,
        app(h, n)
      )
    ) by RightImplies
    thenHave(
      (hIsTheHeightFunction, in(n, N), subset(m, n)) |- forall(
        x,
        in(x, app(h, m)) ==> in(x, app(h, n))
      )
    ) by RightForall
    have(thesis) by Apply(ADTThm.equivalenceRevApply)
      .on(lastStep, subsetAxiom.asInstanceOf)
  }

  /**
   *  Lemma --- There is no element of height 0 in the ADT.
   *
   *  `!∃x ∈ adt. height(x) = 0`
   */
  private val heightZero = Lemma(hIsTheHeightFunction |- !in(x, app(h, ∅))) {

    // This is due to the fact that the extended introduction function is the empty set when the function is empty
    // (which happens when the height is set to 0).
    have(
      hIsTheHeightFunction |- in(x, app(h, ∅)) <=> isInExtendedIntroductionFunctionImage(
        restrictedFunction(h, ∅)
      )(x)
    ) by Cut(ADTThm.zeroIsNat, heightApplication of (n := ∅))
    thenHave(
      (restrictedFunction(h, ∅) === ∅, hIsTheHeightFunction) |- !in(x, app(h, ∅))
    ) by
      RightSubstEq.withParametersSimple(
        List((restrictedFunction(h, ∅), ∅)),
        lambda(s, in(x, app(h, ∅)) <=> isInExtendedIntroductionFunctionImage(s)(x))
      )
    have(thesis) by Cut(ADTThm.restrictedFunctionEmptyDomain, lastStep)
  }

  /**
   *  Lemma --- The set of elements of height n + 1 is the set of elements of height n to
   *  which the introduction function is applied.
   *
   *  `height(n + 1) = introductionFunction(height(n))`
   */
  private val heightSuccessorWeak = Lemma(
    (hIsTheHeightFunction, in(n, N)) |- in(
      x,
      app(h, successor(n))
    ) <=> isInIntroductionFunctionImage(app(h, n))(x)
  ) {

    // STEP 1: Prove that the restriction of height to n + 1 is not empty
    val restrHeightNotEmpty: Expr[Prop] = !(restrictedFunction(h, successor(n)) === ∅)
    have(!(h === ∅) |- restrHeightNotEmpty) by Cut(
      ADTThm.zeroIsNotSucc,
      ADTThm.restrictedFunctionNotEmpty of (d := successor(n))
    )
    val restrHeightNotEmptyLemma = have(
      hIsTheHeightFunction |- restrHeightNotEmpty
    ) by Cut(heightFunctionNonEmpty, lastStep)

    // STEP 2: Use the fact that if the function is cumulative then ∪ range(height | n + 1) = height(n) to conclude the proof
    have(
      (hIsTheHeightFunction, in(n, N)) |- subset(m, n) ==> subset(app(h, m), app(h, n))
    ) by RightImplies(heightMonotonic)
    thenHave(
      (hIsTheHeightFunction, in(n, N)) |- forall(
        m,
        subset(m, n) ==> subset(app(h, m), app(h, n))
      )
    ) by RightForall
    val unionRangeRestr = have(
      (hIsTheHeightFunction, in(n, N)) |- unionRange(
        restrictedFunction(h, successor(n))
      ) === app(h, n)
    ) by Apply(ADTThm.unionRangeCumulativeRestrictedFunction).on(lastStep)

    have(
      (hIsTheHeightFunction, in(n, N)) |- in(
        x,
        app(h, successor(n))
      ) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, successor(n)))(x)
    ) by Apply(heightApplication)
      .on(ADTThm.equivalenceApply of (p1 := in(n, N)), ADTThm.successorIsNat.asInstanceOf)

    thenHave(
      (
        hIsTheHeightFunction,
        in(n, N),
        unionRange(restrictedFunction(h, successor(n))) === app(h, n)
      ) |-
        in(
          x,
          app(h, successor(n))
        ) <=> restrHeightNotEmpty /\ isInIntroductionFunctionImage(app(h, n))(x)
    ) by
      RightSubstEq.withParametersSimple(
        List((unionRange(restrictedFunction(h, successor(n))), app(h, n))),
        lambda(
          s,
          in(x, app(h, successor(n))) <=> (
            restrHeightNotEmpty /\ isInIntroductionFunctionImage(s)(x)
          )
        )
      )

    have(
      (hIsTheHeightFunction, in(n, N)) |- in(
        x,
        app(h, successor(n))
      ) <=> restrHeightNotEmpty /\ isInIntroductionFunctionImage(app(h, n))(x)
    ) by Cut(unionRangeRestr, lastStep)

    have(
      (hIsTheHeightFunction, in(n, N), restrHeightNotEmpty) |- in(
        x,
        app(h, successor(n))
      ) <=> isInIntroductionFunctionImage(app(h, n))(x)
    ) by Apply(ADTThm.equivalenceAnd of (p2 := restrHeightNotEmpty)).on(lastStep)

    have(thesis) by Cut(restrHeightNotEmptyLemma, lastStep)
  }

  // ********
  // * TERM *
  // ********

  /**
   *  Formula describing this ADT's term, i.e. the set of all its instances. It equal to
   *  the union of all the terms that have a height.
   *
   *  `adt = ∪ height(n) = {x | ∃n ∈ N. x ∈ height(n)}`
   *
   *  @param adt the set chracterizing this ADT
   */
  private def termDefinition(adt: Expr[Ind]): Expr[Prop] =
    forall(t, in(t, adt) <=> forall(h, hIsTheHeightFunction ==> in(t, unionRange(h))))

  /**
   *  Lemma --- There exists a unique set satisfying the definition of this ADT
   *
   *  `∃!z. z = ADT
   */
  private val termExistence = Lemma(existsOne(z, termDefinition(z))) {

    // STEP 0: Caching
    val termDefinitionRight = forall(h, hIsTheHeightFunction ==> in(t, unionRange(h)))
    val inUnionRangeF = in(t, unionRange(f))

    // STEP 1: Prove that there exists a term satisfying the definition of this ADT.
    // Specifically, this term is the union of all the terms with a height.
    have(exists(z, termDefinition(z))) subproof {

      // STEP 1.1: Prove the forward implication of the definition, using the uniqueness of the height function
      have(inUnionRangeF |- inUnionRangeF) by Hypothesis
      thenHave((f === h, inUnionRangeF) |- in(t, unionRange(h))) by RightSubstEq
        .withParametersSimple(List((f, h)), lambda(f, inUnionRangeF))
      have(
        (fIsTheHeightFunction, hIsTheHeightFunction, inUnionRangeF) |- in(
          t,
          unionRange(h)
        )
      ) by Cut(heightFunctionUniqueness2, lastStep)
      thenHave(
        (fIsTheHeightFunction, inUnionRangeF) |- hIsTheHeightFunction ==> in(
          t,
          unionRange(h)
        )
      ) by RightImplies
      thenHave(
        (fIsTheHeightFunction, inUnionRangeF) |- termDefinitionRight
      ) by RightForall
      val forward = thenHave(
        fIsTheHeightFunction |- inUnionRangeF ==> termDefinitionRight
      ) by RightImplies

      // STEP 1.2: Prove the backward implication of the definition
      have(termDefinitionRight |- termDefinitionRight) by Hypothesis
      thenHave(
        termDefinitionRight |- fIsTheHeightFunction ==> inUnionRangeF
      ) by InstantiateForall(f)
      val backward =
        thenHave(fIsTheHeightFunction |- termDefinitionRight ==> inUnionRangeF) by Restate

      // STEP 1.3: Use the existence of the height function to prove the existence of this ADT
      have(fIsTheHeightFunction |- inUnionRangeF <=> termDefinitionRight) by RightIff(
        forward,
        backward
      )
      thenHave(
        fIsTheHeightFunction |- forall(t, inUnionRangeF <=> termDefinitionRight)
      ) by RightForall

      thenHave(
        fIsTheHeightFunction |- exists(z, forall(t, in(t, z) <=> termDefinitionRight))
      ) by RightExists
      thenHave(
        exists(f, fIsTheHeightFunction) |- exists(
          z,
          forall(t, in(t, z) <=> termDefinitionRight)
        )
      ) by LeftExists
      have(thesis) by Cut(heightFunctionExistence, lastStep)
    }

    // STEP 2: Conclude using the extension by definition

    have(thesis) by Cut(
      lastStep,
      uniqueByExtension of (schemPred := lambda(t, termDefinitionRight))
    )
  }

  /**
   *  Class function defining the ADT. Takes as parameters the type variables of the ADT
   *  and return the set of all its instances.
   */
  val polymorphicTerm = FunctionDefinition[N](name, line.value, file.value)(
    typeVariablesSeq,
    z,
    termDefinition(z),
    termExistence
  ).label

  /**
   *  The set of all instances of the ADT where the type variables are not instantiated
   *  (i.e. are kept variable).
   */
  val term = polymorphicTerm.applySeq(typeVariablesSeq)

  /** Definition of this ADT's term. */
  private val termDefinition: Expr[Prop] = termDefinition(term)

  /**
   *  Lemma --- This ADT satisfies its definition.
   *
   *  `adt = ∪ height(n)`
   */
  private val termSatisfiesDefinition = Lemma(termDefinition) {
    have(thesis) by InstantiateForall(term)(polymorphicTerm.definition)
  }

  // *************************
  // * TYPING / INTRODUCTION *
  // *************************

  /**
   *  Lemma --- Every element of this ADT has a height. Conversely, if an element has a
   *  height, it is in this ADT.
   *
   *  ` x ∈ ADT <=> ∃n ∈ N. x ∈ height(n)`
   *
   *  TODO: Split into two lemmas
   */
  private val termHasHeight =
    Lemma(hIsTheHeightFunction |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) {

      // STEP 0 : Instantiate the definition of this ADT and recover the forward and backward implications
      val termDefinition = have(
        in(x, term) <=> forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))
      ) by InstantiateForall(x)(termSatisfiesDefinition)
      val termDefinitionForward = have(
        in(x, term) |- forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))
      ) by Cut(
        termDefinition,
        ADTThm.equivalenceApply of (
          p1 := in(x, term),
          p2 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))
        )
      )
      val termDefinitionBackward = have(
        forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- in(x, term)
      ) by Cut(
        termDefinition,
        ADTThm.equivalenceRevApply of (
          p2 := in(x, term),
          p1 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))
        )
      )

      // STEP 1 : Prove that an element is in this ADT if and only if it is in one of the images of the height function.
      have(hIsTheHeightFunction |- in(x, term) <=> in(x, unionRange(h))) subproof {

        // STEP 1.1 : Forward implication
        have(
          forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- forall(
            h,
            hIsTheHeightFunction ==> in(x, unionRange(h))
          )
        ) by Hypothesis
        thenHave(
          forall(
            h,
            hIsTheHeightFunction ==> in(x, unionRange(h))
          ) |- hIsTheHeightFunction ==> in(x, unionRange(h))
        ) by InstantiateForall(h)
        thenHave(
          (
            forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))),
            hIsTheHeightFunction
          ) |- in(x, unionRange(h))
        ) by Restate

        val forward = have(
          hIsTheHeightFunction |- in(x, term) ==> in(x, unionRange(h))
        ) by Apply(lastStep).on(termDefinitionForward)

        // STEP 1.2 : Backward implication, follows from uniqueness of the height function
        have(in(x, unionRange(h)) |- in(x, unionRange(h))) by Hypothesis
        thenHave((f === h, in(x, unionRange(h))) |- in(x, unionRange(f))) by RightSubstEq
          .withParametersSimple(List((f, h)), lambda(h, in(x, unionRange(h))))
        have(
          (fIsTheHeightFunction, hIsTheHeightFunction, in(x, unionRange(h))) |- in(
            x,
            unionRange(f)
          )
        ) by Cut(heightFunctionUniqueness2, lastStep)
        thenHave(
          (hIsTheHeightFunction, in(x, unionRange(h))) |- fIsTheHeightFunction ==> in(
            x,
            unionRange(f)
          )
        ) by RightImplies
        thenHave(
          (hIsTheHeightFunction, in(x, unionRange(h))) |- forall(
            f,
            fIsTheHeightFunction ==> in(x, unionRange(f))
          )
        ) by RightForall
        have((hIsTheHeightFunction, in(x, unionRange(h))) |- in(x, term)) by Cut(
          lastStep,
          termDefinitionBackward
        )
        val backward = thenHave(
          hIsTheHeightFunction |- in(x, unionRange(h)) ==> in(x, term)
        ) by RightImplies

        have(thesis) by RightIff(forward, backward)
      }

      // STEP 2: Conclude by instantiating the union range membership lemma
      have(
        hIsTheHeightFunction |- in(x, term) <=> ∃(
          n,
          in(n, relationDomain(h)) /\ in(x, app(h, n))
        )
      ) by Apply(ADTThm.equivalenceRewriting)
        .on(ADTThm.unionRangeMembership.asInstanceOf, lastStep)

      thenHave(
        (hIsTheHeightFunction, relationDomain(h) === N) |- in(x, term) <=> ∃(
          n,
          in(n, N) /\ in(x, app(h, n))
        )
      ) by RightSubstEq.withParametersSimple(
        List((relationDomain(h), N)),
        lambda(z, in(x, term) <=> ∃(n, in(n, z) /\ in(x, app(h, n))))
      )
    }

  /**
   *  Lemma --- Every element of this ADT has a height. Conversely, if an element has a
   *  height, it is in this ADT.
   *
   *  ` xi, ..., xj ∈ ADT <=> ∃n ∈ N. xi, ..., xj ∈ height(n)`
   *
   *  TODO: Work this out TODO: Split into two lemmas
   */
  private val termsHaveHeight = constructors.map(c =>
    c -> Lemma(
      hIsTheHeightFunction |- (constructorVarsInDomain(c, term) <=> ∃(
        n,
        in(n, N) /\ constructorVarsInDomain(c, app(h, n))
      ))
    ) {

      if c.variables.isEmpty then have(thesis) by Weakening(ADTThm.existsNat)
      else

        // STEP 1: Backward implication

        val backward = have(
          hIsTheHeightFunction |- ∃(
            n,
            in(n, N) /\ constructorVarsInDomain(c, app(h, n))
          ) ==> constructorVarsInDomain(c, term)
        ) subproof {
          val andSeq =
            for (v, ty) <- c.signature yield ty match
              case Self =>
                val termHasHeightBackward = have(
                  (hIsTheHeightFunction, exists(n, in(n, N) /\ in(v, app(h, n)))) |- in(
                    v,
                    term
                  )
                ) by Cut(
                  termHasHeight of (x := v),
                  ADTThm.equivalenceRevApply of (
                    p1 := ∃(n, in(n, N) /\ in(v, app(h, n))),
                    p2 := in(v, term)
                  )
                )

                have(
                  (in(n, N) /\ in(v, app(h, n))) |- in(n, N) /\ in(v, app(h, n))
                ) by Restate
                thenHave(
                  (
                    in(n, N) /\ in(v, app(h, n))
                  ) |- exists(n, in(n, N) /\ in(v, app(h, n)))
                ) by RightExists
                have(
                  (hIsTheHeightFunction, in(n, N) /\ in(v, app(h, n))) |- in(v, term)
                ) by Cut(lastStep, termHasHeightBackward)
                thenHave(
                  (
                    hIsTheHeightFunction,
                    in(n, N) /\ constructorVarsInDomain(c, app(h, n))
                  ) |- in(v, term)
                ) by Weakening
              case GroundType(t) => have(
                  (
                    hIsTheHeightFunction,
                    in(n, N) /\ constructorVarsInDomain(c, app(h, n))
                  ) |- in(v, t)
                ) by Restate

          have(
            (
              hIsTheHeightFunction,
              in(n, N) /\ constructorVarsInDomain(c, app(h, n))
            ) |- constructorVarsInDomain(c, term)
          ) by RightAnd(andSeq*)
          thenHave(
            (
              hIsTheHeightFunction,
              exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
            ) |- constructorVarsInDomain(c, term)
          ) by LeftExists
        }

        // STEP 2: Forward implication

        val forward = have(
          hIsTheHeightFunction |- constructorVarsInDomain(c, term) ==> ∃(
            n,
            in(n, N) /\ constructorVarsInDomain(c, app(h, n))
          )
        ) subproof {
          val nSeq: Seq[Variable[Ind]] = (0 until c.variables.size)
            .map(i => Variable[Ind](s"n$i"))
          val max = if c.arity == 0 then ∅ else nSeq.reduce[Expr[Ind]](setUnion(_, _))

          val maxInN = have(/\(nSeq.map(n => in(n, N))) |- in(max, N)) by Sorry

          val andSeq =
            for ((v, ty), ni) <- c.signature.zip(nSeq) yield
              val niInMax = have(subset(ni, max)) by Sorry

              ty match
                case Self =>
                  have(
                    (hIsTheHeightFunction, in(max, N), subset(ni, max)) |- subset(
                      app(h, ni),
                      app(h, max)
                    )
                  ) by Restate.from(heightMonotonic of (m := ni, n := max))
                  have(
                    (hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- subset(
                      app(h, ni),
                      app(h, max)
                    )
                  ) by Sorry // Apply(lastStep).on(Seq(maxInN, niInMax), excluding = nSeq)
                  have(
                    (hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- forall(
                      z,
                      in(z, app(h, ni)) ==> in(z, app(h, max))
                    )
                  ) by Apply(ADTThm.equivalenceApply)
                    .on(Seq(lastStep, subsetAxiom), excluding = nSeq)
                  thenHave(
                    (hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- in(
                      v,
                      app(h, ni)
                    ) ==> in(v, app(h, max))
                  ) by InstantiateForall(v)
                  thenHave(
                    (
                      hIsTheHeightFunction,
                      /\(nSeq.map(n => in(n, N))),
                      in(v, app(h, ni))
                    ) |- in(v, app(h, max))
                  ) by Restate
                case GroundType(t) => have(
                    (/\(nSeq.map(n => in(n, N))), hIsTheHeightFunction, in(v, t)) |- in(
                      v,
                      t
                    )
                  ) by Restate

              have(
                (
                  /\(nSeq.map(n => in(n, N))),
                  hIsTheHeightFunction,
                  in(v, ty.getOrElse(app(h, ni)))
                ) |- in(max, N) /\ in(v, ty.getOrElse(app(h, max)))
              ) by RightAnd(maxInN, lastStep)
              thenHave(
                nSeq.map(n => in(n, N) /\ in(v, ty.getOrElse(app(h, n))))
                  .toSet + hIsTheHeightFunction |- in(max, N) /\ in(
                  v,
                  ty.getOrElse(app(h, max))
                )
              ) by Weakening
              thenHave(
                nSeq.map(n => in(n, N) /\ in(v, ty.getOrElse(app(h, n))))
                  .toSet + hIsTheHeightFunction |- ∃(
                  n,
                  in(n, N) /\ in(v, ty.getOrElse(app(h, n)))
                )
              ) by RightExists

          sorry
        }

        // STEP 3: Conclude
        have(thesis) by RightIff(forward, backward)
    }
  ).toMap

  /**
   *  Lemma --- If all inductive arguments of a constructor have height below n then the
   *  instance of this constructor has height below n + 1.
   *
   *  ` xi, ..., xj ∈ height(n) |- c(x1, ..., xn) ∈ height(n + 1)`
   */
  private val heightConstructor = constructors.map(c =>
    c -> Lemma(
      (hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(
        c.term,
        app(h, successor(n))
      )
    ) {

      // Caching
      val constructorInIntroFunHeight = isInIntroductionFunctionImage(app(h, n))(c.term)

      // Chaining the lemma on the elements of height n + 1 and the one on constructors being in the image of the introduction function
      have(
        (hIsTheHeightFunction, in(n, N), constructorInIntroFunHeight) |- in(
          c.term,
          app(h, successor(n))
        )
      ) by Cut(
        heightSuccessorWeak of (x := c.term),
        ADTThm.equivalenceRevApply of (
          p1 := constructorInIntroFunHeight,
          p2 := in(c.term, app(h, successor(n)))
        )
      )
      have(
        (hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(
          c.term,
          app(h, successor(n))
        )
      ) by Cut(constructorIsInIntroductionFunction(c) of (s := app(h, n)), lastStep)
    }
  ).toMap

  /**
   *  Lemma --- If all inductive arguments of a constructor are in this ADT, and the non
   *  inductive ones in their respective domain, then the instance of this constructor is
   *  in this ADT as well. Also known as introduction rules.
   *
   *  ` xi, ..., xj ∈ ADT |- c(x1, ..., xn) ∈ ADT`
   */
  val intro = constructors.map(c =>
    c ->
      Lemma(simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))) {
        // STEP 0: Instantiate the forward direction of termsHaveHeight.
        val termsHaveHeightForward = have(
          (hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- ∃(
            n,
            in(n, N) /\ constructorVarsInDomain(c, app(h, n))
          )
        ) by Cut(
          termsHaveHeight(c),
          ADTThm.equivalenceApply of (
            p1 := constructorVarsInDomain(c, term),
            p2 := exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
          )
        )

        // STEP 1: Prove that if an instance of a constructor has height n + 1 then it is in this ADT.
        val left = have(in(n, N) |- in(successor(n), N)) by Cut(
          ADTThm.successorIsNat,
          ADTThm.equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N))
        )
        val right = have(
          in(c.term, app(h, successor(n))) |- in(c.term, app(h, successor(n)))
        ) by Hypothesis
        have(
          (in(n, N), in(c.term, app(h, successor(n)))) |- in(successor(n), N) /\ in(
            c.term,
            app(h, successor(n))
          )
        ) by RightAnd(left, right)
        thenHave(
          (in(n, N), in(c.term, app(h, successor(n)))) |- exists(
            m,
            in(m, N) /\ in(c.term, app(h, m))
          )
        ) by RightExists
        have(
          (hIsTheHeightFunction, in(n, N), in(c.term, app(h, successor(n)))) |- in(
            c.term,
            term
          )
        ) by Apply(ADTThm.equivalenceRevApply).on(lastStep, termHasHeight.asInstanceOf)

        // STEP 2: Prove that if the inductive arguments of the constructor have height then the instance of the constructor is in the ADT.
        have(
          (hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(
            c.term,
            term
          )
        ) by Cut(heightConstructor(c), lastStep)

        // STEP 3: Prove that if the inductive arguments of the constructor are in the ADT then they have a height and therefore
        // the instance of the constructor is in the ADT.
        thenHave(
          (hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(
            c.term,
            term
          )
        ) by LeftAnd
        thenHave(
          (
            hIsTheHeightFunction,
            exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
          ) |- in(c.term, term)
        ) by LeftExists
        have(
          (hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- in(c.term, term)
        ) by Cut(termsHaveHeightForward, lastStep)

        // STEP 4: Remove lingering assumptions
        thenHave(
          (exists(h, hIsTheHeightFunction), constructorVarsInDomain(c, term)) |- in(
            c.term,
            term
          )
        ) by LeftExists
        have(constructorVarsInDomain(c, term) |- in(c.term, term)) by Cut(
          heightFunctionExistence,
          lastStep
        )
      }
  ).toMap

  // ************************
  // * STRUCTURAL INDUCTION *
  // ************************

  /**
   *  Lemma --- An element has height n + 1 if and only if it is the instance of some
   *  constructor with inductive arguments of height n.
   *
   *  ` x ∈ height(n + 1) <=> x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n)`
   */
  private lazy val heightSuccessorStrong = Lemma(
    (hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isConstructor(
      x,
      app(h, n)
    )
  ) {
    val forward = have(
      (hIsTheHeightFunction, in(n, N)) |- isInIntroductionFunctionImage(
        app(h, n)
      )(x) ==> isConstructor(x, app(h, n))
    ) subproof {

      def inductionFormula(n: Expr[Ind]): Expr[Prop] =
        isInIntroductionFunctionImage(app(h, n))(x) ==> isConstructor(x, app(h, n))
      val inductionFormulaN: Expr[Prop] = inductionFormula(n)
      val inductionFormulaSuccN: Expr[Prop] = inductionFormula(successor(n))

      // STEP 1.1 : Base case
      val isContructorXHEmptySet = isConstructor(x, app(h, ∅))
      val baseCaseLeft =
        have(isContructorXHEmptySet |- isContructorXHEmptySet) by Hypothesis
      val baseCaseRight = have((hIsTheHeightFunction, in(x, app(h, ∅))) |- ()) by Restate
        .from(heightZero)
      have(
        (
          hIsTheHeightFunction,
          isInIntroductionFunctionImage(app(h, ∅))(x)
        ) |- isContructorXHEmptySet
      ) by LeftOr(baseCaseLeft, baseCaseRight)
      thenHave(
        hIsTheHeightFunction |- isInIntroductionFunctionImage(
          app(h, ∅)
        )(x) ==> isContructorXHEmptySet
      ) by RightImplies
      val inductiveCaseRemaining = have(
        (
          hIsTheHeightFunction,
          forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))
        ) |- forall(n, in(n, N) ==> inductionFormulaN)
      ) by Cut(lastStep, ADTThm.natInduction of (P := lambda(n, inductionFormulaN)))

      // STEP 1.2: Unfolding the definition of subset
      have(
        subset(app(h, n), app(h, successor(n))) |- forall(
          z,
          in(z, app(h, n)) ==> in(z, app(h, successor(n)))
        )
      ) by Cut(
        subsetAxiom of (x := app(h, n), y := app(h, successor(n))),
        ADTThm.equivalenceApply of (
          p1 := subset(app(h, n), app(h, successor(n))),
          p2 := forall(z, in(z, app(h, n)) ==> in(z, app(h, successor(n))))
        )
      )
      val subsetElimination = thenHave(
        subset(app(h, n), app(h, successor(n))) |- in(y, app(h, n)) ==> in(
          y,
          app(h, successor(n))
        )
      ) by InstantiateForall(y)

      // STEP 1.3 : Use monotonicity to prove that y ∈ height(n) => y ∈ height(n + 1)
      have(in(n, N) |- in(successor(n), N)) by Cut(
        ADTThm.successorIsNat,
        ADTThm.equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N))
      )
      have(
        (hIsTheHeightFunction, in(n, N), subset(n, successor(n))) |- subset(
          app(h, n),
          app(h, successor(n))
        )
      ) by Cut(lastStep, heightMonotonic of (n := successor(n), m := n))
      have(
        (hIsTheHeightFunction, in(n, N)) |- subset(app(h, n), app(h, successor(n)))
      ) by Cut(ADTThm.subsetSuccessor, lastStep)
      val liftHeight = have(
        (hIsTheHeightFunction, in(n, N)) |- in(y, app(h, n)) ==> in(
          y,
          app(h, successor(n))
        )
      ) by Cut(lastStep, subsetElimination)

      // STEP 1.4 : Generalize the above result to show that if for some c, x = c(x1, ..., xn) with xi, ..., xj ∈ height(n)
      // then for some c', x = c'(x1, ..., xn) with xi, ..., xj ∈ height(n + 1).

      // Caching
      val isConstructorXHN = isConstructor(x, app(h, n))
      val isConstructorXHSuccN = isConstructor(x, app(h, successor(n)))
      val liftConstructorHeight =
        if constructors.size == 0 then
          have(
            (hIsTheHeightFunction, in(n, N), isConstructorXHN) |- isConstructorXHSuccN
          ) by Restate
        else
          val liftConstructorHeightOrSequence =
            for c <- constructors yield

              // Caching
              val isConstructorCXHN = isConstructor(c, x, app(h, n))
              val isConstructorCXHSuccN = isConstructor(c, x, app(h, successor(n)))
              val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
              val constructorVarsInHSuccN =
                constructorVarsInDomain(c, app(h, successor(n)))

              if c.arity == 0 then
                have(
                  (
                    hIsTheHeightFunction,
                    in(n, N),
                    isConstructorCXHN
                  ) |- isConstructorCXHSuccN
                ) by Restate
              else
                val liftHeightAndSequence =
                  for (v, ty) <- c.signature
                  yield have(
                    (hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(
                      v,
                      ty.getOrElse(app(h, successor(n)))
                    )
                  ) by Weakening(liftHeight of (y := v))

                val left = have(
                  (
                    hIsTheHeightFunction,
                    in(n, N),
                    constructorVarsInHN
                  ) |- constructorVarsInHSuccN
                ) by RightAnd(liftHeightAndSequence*)
                val right = have(x === c.term |- x === c.term) by Hypothesis

                have(
                  (
                    hIsTheHeightFunction,
                    in(n, N),
                    constructorVarsInHN,
                    (x === c.term)
                  ) |- constructorVarsInHSuccN /\ (x === c.term)
                ) by RightAnd(left, right)
                thenHave(
                  (
                    hIsTheHeightFunction,
                    in(n, N),
                    constructorVarsInHN /\ (x === c.term)
                  ) |- constructorVarsInHSuccN /\ (x === c.term)
                ) by LeftAnd
                thenHave(
                  (
                    hIsTheHeightFunction,
                    in(n, N),
                    constructorVarsInHN /\ (x === c.term)
                  ) |- isConstructorCXHSuccN
                ) by QuantifiersIntro(c.variables)
                thenHave(
                  (
                    hIsTheHeightFunction,
                    in(n, N),
                    isConstructorCXHN
                  ) |- isConstructorCXHSuccN
                ) by QuantifiersIntro(c.variables)

              thenHave(
                (
                  hIsTheHeightFunction,
                  in(n, N),
                  isConstructorCXHN
                ) |- isConstructorXHSuccN
              ) by Weakening

          have(
            (hIsTheHeightFunction, in(n, N), isConstructorXHN) |- isConstructorXHSuccN
          ) by LeftOr(liftConstructorHeightOrSequence*)

      // STEP 1.5: Show that x ∈ introductionFunction(height(n + 1)) => for some c, x = c(x1, ..., xn)
      // with xi, ..., xj ∈ height(n + 1).
      val heightSuccessorWeakForward = have(
        (
          hIsTheHeightFunction,
          in(n, N),
          in(x, app(h, successor(n)))
        ) |- isInIntroductionFunctionImage(app(h, n))(x)
      ) by Cut(
        heightSuccessorWeak,
        ADTThm.equivalenceApply of (
          p1 := in(x, app(h, successor(n))),
          p2 := isInIntroductionFunctionImage(app(h, n))(x)
        )
      )
      have(
        (
          inductionFormulaN,
          isInIntroductionFunctionImage(app(h, n))(x)
        ) |- isConstructorXHN
      ) by Restate
      have(
        (
          hIsTheHeightFunction,
          in(n, N),
          in(x, app(h, successor(n))),
          inductionFormulaN
        ) |- isConstructorXHN
      ) by Cut(heightSuccessorWeakForward, lastStep)
      val right = have(
        (
          hIsTheHeightFunction,
          in(n, N),
          in(x, app(h, successor(n))),
          inductionFormulaN
        ) |- isConstructorXHSuccN
      ) by Cut(lastStep, liftConstructorHeight)
      val left = have(isConstructorXHSuccN |- isConstructorXHSuccN) by Hypothesis
      have(
        (
          hIsTheHeightFunction,
          in(n, N),
          inductionFormulaN,
          isInIntroductionFunctionImage(app(h, successor(n)))(x)
        ) |- isConstructorXHSuccN
      ) by LeftOr(left, right)

      // STEP 1.6: Conclude
      thenHave(
        (hIsTheHeightFunction, in(n, N), inductionFormulaN) |- inductionFormulaSuccN
      ) by RightImplies
      thenHave(
        (hIsTheHeightFunction, in(n, N)) |- inductionFormulaN ==> inductionFormulaSuccN
      ) by RightImplies
      thenHave(
        hIsTheHeightFunction |- in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)
      ) by RightImplies
      thenHave(
        hIsTheHeightFunction |- forall(
          n,
          in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)
        )
      ) by RightForall
      have(hIsTheHeightFunction |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(
        lastStep,
        inductiveCaseRemaining
      )
      thenHave(
        hIsTheHeightFunction |- in(n, N) ==> inductionFormulaN
      ) by InstantiateForall(n)
    }

    // STEP 2: Prove the backward implication
    val backward = have(
      (hIsTheHeightFunction, in(n, N)) |- isConstructor(
        x,
        app(h, n)
      ) ==> isInIntroductionFunctionImage(app(h, n))(x)
    ) by Restate

    // STEP 3: Conclude
    have(
      (hIsTheHeightFunction, in(n, N)) |- isInIntroductionFunctionImage(
        app(h, n)
      )(x) <=> isConstructor(x, app(h, n))
    ) by RightIff(forward, backward)
    have(thesis) by Apply(ADTThm.equivalenceRewriting)
      .on(lastStep, heightSuccessorWeak.asInstanceOf)
  }

  /**
   *  Generates the structural inductive case for a given constructor.
   *
   *  @param c the constructor
   */
  lazy val inductiveCase: Map[SyntacticConstructor, Expr[Prop]] = constructors.map(c =>
    c -> c.signature.foldRight[Expr[Prop]](P(c.term))((el, fc) =>
      val (v, ty) = el
      ty match
        case Self => forall(v, in(v, term) ==> (P(v) ==> fc))
        case GroundType(t) => forall(v, in(v, t) ==> fc)
    )
  ).toMap

  /**
   *  Lemma --- Structural induction principle for this ADT.
   *
   *  `base cases => inductive cases => ∀x ∈ ADT. P(x)`
   */
  lazy val induction = Lemma(
    constructors.foldRight[Expr[Prop]](forall(x, in(x, term) ==> P(x)))((c, f) =>
      inductiveCase(c) ==> f
    )
  ) {

    // List of cases to prove for structural induction to hold
    val structuralInductionPreconditions: Expr[Prop] = Utils
      ./\(constructors.map(inductiveCase))

    // We want to prove the claim by induction on the height of n, i.e. prove that for any
    // n in N, P holds.
    def inductionFormula(n: Expr[Ind]): Expr[Prop] = forall(x, in(x, app(h, n)) ==> P(x))
    val inductionFormulaN: Expr[Prop] = inductionFormula(n)

    // STEP 1: Prove the base case
    have(hIsTheHeightFunction |- in(x, app(h, ∅)) ==> P(x)) by Weakening(heightZero)
    val zeroCase = thenHave(hIsTheHeightFunction |- inductionFormula(∅)) by RightForall

    val inductiveCaseRemaining = have(
      (
        hIsTheHeightFunction,
        forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n))))
      ) |- forall(n, in(n, N) ==> inductionFormulaN)
    ) by Cut(zeroCase, ADTThm.natInduction of (P := lambda(n, inductionFormulaN)))

    // STEP 2: Prove the inductive case
    val succCase = have(
      (hIsTheHeightFunction, structuralInductionPreconditions) |- forall(
        n,
        in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n)))
      )
    ) subproof {

      // STEP 2.1 : Prove that if the x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n) then P(x) holds.
      val isConstructorImpliesP = have(
        (
          hIsTheHeightFunction,
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN,
          isConstructor(x, app(h, n))
        ) |- P(x)
      ) subproof {

        if constructors.isEmpty then have(thesis) by Restate
        else
          val orSeq = (for c <- constructors yield

            // Caching
            val constructorPrecondition = inductiveCase(c)
            val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
            val constructorVarsInHNEx =
              ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
            val constructorVarsInTerm = constructorVarsInDomain(c, term)

            // STEP 2.1.1: Prove that if xi, ..., xj ∈ height(n) then xi, ..., xj ∈ ADT.
            val constructorQuantVarsInHNToTerm = have(
              (
                hIsTheHeightFunction,
                in(n, N),
                constructorVarsInHN
              ) |- constructorVarsInTerm
            ) subproof {
              have(
                (hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(
                  n,
                  N
                ) /\ constructorVarsInHN
              ) by Restate
              val consVarL = thenHave(
                (
                  hIsTheHeightFunction,
                  in(n, N),
                  constructorVarsInHN
                ) |- constructorVarsInHNEx
              ) by RightExists
              have(
                (
                  constructorVarsInTerm <=> constructorVarsInHNEx,
                  constructorVarsInHNEx
                ) |- constructorVarsInTerm
              ) by Restate.from(
                ADTThm.equivalenceRevApply of (
                  p1 := constructorVarsInTerm,
                  p2 := constructorVarsInHNEx
                )
              )
              have(
                (hIsTheHeightFunction, constructorVarsInHNEx) |- constructorVarsInTerm
              ) by Cut(termsHaveHeight(c), lastStep)
              have(thesis) by Cut(consVarL, lastStep)
            }

            // STEP 2.1.2: Prove that if xi, ..., xj ∈ height(n) then P(c(x1, ..., xn)).
            have(
              (
                hIsTheHeightFunction,
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN
              ) |- constructorPrecondition
            ) by Restate

            c.signature.foldLeft(lastStep)((fact, el) =>
              val (v, ty) = el

              fact.statement.right.head match
                case Forall(_, factCclWithoutForall) =>
                  thenHave(
                    (
                      hIsTheHeightFunction,
                      constructorPrecondition,
                      in(n, N),
                      inductionFormulaN,
                      constructorVarsInHN
                    ) |- factCclWithoutForall
                  ) by InstantiateForall(v)

                  factCclWithoutForall match
                    case Implies(membership, subformula) => ty match
                        case Self => subformula match
                            case Implies(hypothesis, subSubFormula) =>
                              val proofSubSubFormula = thenHave(
                                (
                                  hIsTheHeightFunction,
                                  constructorPrecondition,
                                  in(n, N),
                                  inductionFormulaN,
                                  constructorVarsInTerm,
                                  constructorVarsInHN,
                                  P(v)
                                ) |- subSubFormula
                              ) by Weakening

                              have(inductionFormulaN |- inductionFormulaN) by Hypothesis
                              thenHave(
                                inductionFormulaN |- in(v, app(h, n)) ==> P(v)
                              ) by InstantiateForall(v)
                              thenHave(
                                (inductionFormulaN, constructorVarsInHN) |- P(v)
                              ) by Weakening

                              have(
                                (
                                  hIsTheHeightFunction,
                                  constructorPrecondition,
                                  in(n, N),
                                  inductionFormulaN,
                                  constructorVarsInTerm,
                                  constructorVarsInHN
                                ) |- subSubFormula
                              ) by Cut(lastStep, proofSubSubFormula)
                              have(
                                (
                                  hIsTheHeightFunction,
                                  constructorPrecondition,
                                  in(n, N),
                                  inductionFormulaN,
                                  constructorVarsInHN
                                ) |- subSubFormula
                              ) by Cut(constructorQuantVarsInHNToTerm, lastStep)

                            case _ => throw UnreachableException

                        case GroundType(t) => thenHave(
                            (
                              hIsTheHeightFunction,
                              constructorPrecondition,
                              in(n, N),
                              inductionFormulaN,
                              constructorVarsInHN
                            ) |- subformula
                          ) by Restate
                    case _ => throw UnreachableException
                case _ => throw UnreachableException
            )

            thenHave(
              (
                hIsTheHeightFunction,
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN
              ) |- P(c.term)
            ) by Restate

            // STEP 2.1.3: Prove that if xi, ..., xj ∈ height(n) then P(x).
            thenHave(
              (
                hIsTheHeightFunction,
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN,
                x === c.term
              ) |- P(x)
            ) by RightSubstEq.withParametersSimple(List((x, c.term)), lambda(x, P(x)))

            thenHave(
              (
                hIsTheHeightFunction,
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN /\ (x === c.term)
              ) |- P(x)
            ) by LeftAnd

            thenHave(
              (
                hIsTheHeightFunction,
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                isConstructor(c, x, app(h, n))
              ) |- P(x)
            ) by QuantifiersIntro(c.variables)
            thenHave(
              (
                hIsTheHeightFunction,
                structuralInductionPreconditions,
                in(n, N),
                inductionFormulaN,
                isConstructor(c, x, app(h, n))
              ) |- P(x)
            ) by Weakening
          ).toSeq

          have(
            (
              hIsTheHeightFunction,
              structuralInductionPreconditions,
              in(n, N),
              inductionFormulaN,
              isConstructor(x, app(h, n))
            ) |- P(x)
          ) by LeftOr(orSeq*)
      }

      // STEP 2.2: Prove that if x ∈ height(n + 1) then P(x) holds.
      have(
        (hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n)))) |- isConstructor(
          x,
          app(h, n)
        )
      ) by Cut(
        heightSuccessorStrong,
        ADTThm.equivalenceApply of (
          p1 := in(x, app(h, successor(n))),
          p2 := isConstructor(x, app(h, n))
        )
      )
      have(
        (
          hIsTheHeightFunction,
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN,
          in(x, app(h, successor(n)))
        ) |- P(x)
      ) by Cut(lastStep, isConstructorImpliesP)

      // STEP 2.3: Conclude
      thenHave(
        (
          hIsTheHeightFunction,
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN
        ) |- in(x, app(h, successor(n))) ==> P(x)
      ) by RightImplies

      thenHave(
        (
          hIsTheHeightFunction,
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN
        ) |- inductionFormula(successor(n))
      ) by RightForall
      thenHave(
        (
          hIsTheHeightFunction,
          structuralInductionPreconditions,
          in(n, N)
        ) |- inductionFormulaN ==> inductionFormula(successor(n))
      ) by RightImplies
      thenHave(
        (hIsTheHeightFunction, structuralInductionPreconditions) |- in(n, N) ==> (
          inductionFormulaN ==> inductionFormula(successor(n))
        )
      ) by RightImplies
      thenHave(thesis) by RightForall
    }

    // STEP 3: Conclude

    have(
      (hIsTheHeightFunction, structuralInductionPreconditions) |- forall(
        n,
        in(n, N) ==> inductionFormulaN
      )
    ) by Cut(lastStep, inductiveCaseRemaining)
    thenHave(
      (hIsTheHeightFunction, structuralInductionPreconditions) |- in(
        n,
        N
      ) ==> inductionFormulaN
    ) by InstantiateForall(n)
    thenHave(
      (
        hIsTheHeightFunction,
        structuralInductionPreconditions,
        in(n, N)
      ) |- inductionFormulaN
    ) by Restate
    thenHave(
      (hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- in(
        x,
        app(h, n)
      ) ==> P(x)
    ) by InstantiateForall(x)
    thenHave(
      (
        hIsTheHeightFunction,
        structuralInductionPreconditions,
        in(n, N) /\ in(x, app(h, n))
      ) |- P(x)
    ) by Restate
    val exImpliesP = thenHave(
      (
        hIsTheHeightFunction,
        structuralInductionPreconditions,
        exists(n, in(n, N) /\ in(x, app(h, n)))
      ) |- P(x)
    ) by LeftExists
    have(
      (hIsTheHeightFunction, in(x, term)) |- exists(n, in(n, N) /\ in(x, app(h, n)))
    ) by Cut(
      termHasHeight,
      ADTThm.equivalenceApply of (
        p1 := in(x, term),
        p2 := exists(n, in(n, N) /\ in(x, app(h, n)))
      )
    )

    have(
      (hIsTheHeightFunction, structuralInductionPreconditions, in(x, term)) |- P(x)
    ) by Cut(lastStep, exImpliesP)
    thenHave(
      (
        exists(h, hIsTheHeightFunction),
        structuralInductionPreconditions,
        in(x, term)
      ) |- P(x)
    ) by LeftExists
    have((structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(
      heightFunctionExistence,
      lastStep
    )
    thenHave(structuralInductionPreconditions |- in(x, term) ==> P(x)) by RightImplies
    thenHave(
      structuralInductionPreconditions |- forall(x, in(x, term) ==> P(x))
    ) by RightForall
  }

}
