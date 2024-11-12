/**
 * This file implements tactics to generate polymorphic set theoretic inductive algebraic data types (or ADT) and prove properties about them.
 * An algebraic data type is the least set closed under introduction rules, also known as constructors.
 * A constructor takes arguments as input that can either belong to other types (non inductive arguments)
 * or to the ADT itself (inductive arguments).
 *
 * An example of algebraic data type is the type of singly linked lists:
 *
 *   list ::= nil() | cons(head: T, tail: list)
 */

package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{*, given}
import lisa.maths.settheory.functions.*
import Helpers.*
import Helpers.{/\, \/, ===}
import ADTDefinitions.*
import ADTHelperTheorems as ADTThm
import ADTThm.{N, pair, pairExtensionality}
import lisa.maths.settheory.functions.|=>
import lisa.maths.settheory.types.TypeSystem.{ :: }
import lisa.maths.Quantifiers.{universalEquivalenceDistribution}
import lisa.fol.FOL.Variable

/**
 * Helpers for constructors
 */
private object Constructors {

  /**
   * Global counter used to uniquely identify constructors and thereby avoid structural subtyping.
   */
  var tagCounter = 0
}

/**
 * Syntactic set theoretical interpretation of a constructor for an algebraic data type.
 * In set theory, a constructor is a tuple containing the arguments it has been applied to, in addition to a tag
 * uniquely identifying it.
 * 
 * E.g. `cons(1, nil())` is represented as `(tagcons, (1, ((tagnil, ∅), ∅)))`
 * 
 * Constructors injectivity is proved within this class.
 *
 * @constructor creates a new constructor out of a user specification
 * @param specification types that the constructor takes as arguments
 * @param variables1 variables used to represent the arguments of the constructor
 * @param variables2 alternative set of variables to avoid capture issues
 */
private class SyntacticConstructor(
  val specification: Seq[ConstructorArgument], 
  val variables1: Seq[Variable], 
  val variables2: Seq[Variable],
  ) {

  /**
   * Unique identifier of this constructor
   */
  val tag: Int = Constructors.tagCounter
  Constructors.tagCounter = Constructors.tagCounter + 1

  /**
   * Term representation of the tag of this constructor
   */
  val tagTerm: Term = toTerm(tag)

  /**
    * Sequence of variables used to represent the arguments of the constructor
    */
  val variables: Seq[Variable] = variables1

  /**
   * Number of arguments that this constructor takes
   */
  val arity: Int = specification.length
  
  /**
   * Sequence of variables of the constructor with their respective domains.
   */
  val signature1: Seq[(Variable, ConstructorArgument)] = variables1.zip(specification)

  /**
   * Alternative sequence of variables of the constructor with their respective domains.
   */
  val signature2: Seq[(Variable, ConstructorArgument)] = variables2.zip(specification)

  /**
   * Sequence of variables of the constructor with their respective domains.
   */
  val signature: Seq[(Variable, ConstructorArgument)] = signature1

  /**
   * Internally, an instance of this constructor is represented as a list.
   * The first element of this list is the tag of this constructor.
   * The following elements are its arguments. We represent lists as chained
   * pairs followed by the empty set.
   *
   * e.g. cons(1, nil()) --> (tagcons, (1, ((tagnil, ∅), ∅)))
   *
   * @param args the arguments of this instance of the constructor
   */
  def term(args: Seq[Term]): Term = pair(tagTerm, subterm(args))

  /**
    * Internal representation of an instance of this constructor in which arguments are schematic variables.
    */
  val term1: Term = term(variables1)

  /**
    * Internal representation of an instance of this constructor in which arguments are an alternative set of schematic variables.
    */
  val term2: Term = term(variables2)

  /**
    * Internal representation of an instance of this constructor in which arguments are schematic variables.
    */
  val term: Term = term1

  /**
   * Internal representation of an instance of this constructor without the tag
   *
   * @param args the arguments of this instance of the constructor
   *
   * @see [[this.term]]
   */
  def subterm(args: Seq[Term]): Term = args.foldRight[Term](emptySet)(pair(_, _))

  /**
   * Internal representation of an instance of this constructor without the tag, in which arguments are schematic variables.
   */
  val subterm1: Term = subterm(variables1)

  /**
   * Internal representation of an instance of this constructor without the tag, in which arguments are an alternative set 
   * of schematic variables.
   */
  val subterm2: Term = subterm(variables2)

  /**
   * Internal representation of an instance of this constructor without the tag, in which arguments are schematic variables.
   */
  val subterm: Term = subterm1

  /**
   * Theorem --- Injectivity of constructors.
   *
   *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
   *
   * e.g. cons(head1, tail1) === cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
   */
  lazy val injectivity =
    if arity == 0 then
      Lemma(term1 === term2) {
        have(thesis) by RightRefl
      }
    else
      Lemma((term1 === term2) <=> (variables1 === variables2)) {

        // STEP 1: Get rid of the tag using pair extensionality
        have((term1 === term2) <=> (subterm1 === subterm2)) by Restate.from(pairExtensionality of (a := tagTerm, b := subterm1, c := tagTerm, d := subterm2))

        // STEP 2: Repeat pair extensionality until all variables have been pulled out of the term
        variables1
          .zip(variables2)
          .foldLeft(Seq.empty[Variable], variables1, Seq.empty[Variable], variables2, lastStep)((acc, v) =>

            // pulledVars1 are the variables that have been pulled out of the left term
            // remainingVars1 are the variables that are still in the left term
            // pulledVars2 are the variables that have been pulled out of the right term
            // remainingVars2 are the variables that are still in the right term
            val (pulledVars1, remainingVars1, pulledVars2, remainingVars2, previousFact) = acc

            // v1 and v2 are the variables that are being pulled out
            val (v1, v2) = v

            val updatedPulledVars1 = pulledVars1 :+ v1
            val updatedPulledVars2 = pulledVars2 :+ v2
            val updatedRemainingVars1 = remainingVars1.tail
            val updatedRemainingVars2 = remainingVars2.tail

            val subsubterm1 = subterm(updatedRemainingVars1)
            val subsubterm2 = subterm(updatedRemainingVars2)

            have(
              (pair(v1, subsubterm1) === pair(v2, subsubterm2)) <=>
                ((v1 === v2) /\ (subsubterm1 === subsubterm2))
            ) by Restate.from(pairExtensionality of (a := v1, b := subsubterm1, c := v2, d := subsubterm2))
            have(
              ((pulledVars1 === pulledVars2) /\ (pair(v1, subsubterm1) === pair(v2, subsubterm2))) <=>
                ((pulledVars1 === pulledVars2) /\ (v1 === v2) /\ (subsubterm1 === subsubterm2))
            ) by Cut(
              lastStep,
              ADTThm.rightAndEquivalence of (p := pulledVars1 === pulledVars2, p1 := pair(v1, subsubterm1) === pair(v2, subsubterm2), p2 := (v1 === v2) /\ (subsubterm1 === subsubterm2))
            )
            val newFact = have(
              (term1 === term2) <=>
                ((updatedPulledVars1 === updatedPulledVars2) /\ (subsubterm1 === subsubterm2))
            ) by Apply(ADTThm.equivalenceRewriting).on(lastStep, previousFact)

            (updatedPulledVars1, updatedRemainingVars1, updatedPulledVars2, updatedRemainingVars2, newFact)
          )
      }
    
}

/**
  * Syntactic set theoretical interpretation of an algebraic data type. That is the least set closed under [[SyntacticConstructor]].
  * 
  * E.g. list is the smallest set containing nil and closed under the syntactic operation cons.
  * 
  * Injectivity between different constructors, introduction rules and structural induction are proved within this class.
  *
  * @constructor creates a new algebraic data type out of a user specification.
  * @param line the line at which the ADT is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param file the file in which the ADT is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param name the name of the ADT
  * @param constructors constructors of the ADT
  * @param typeVariables type variables used in the definition of this ADT
  */
private class SyntacticADT[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
  val name: String, 
  val constructors: Seq[SyntacticConstructor],
  val typeVariables: Variable ** N,
  ) {

  /**
   * Sequence of type variables used in the definition of this ADT
   */
  val typeVariablesSeq: Seq[Variable] = typeVariables.toSeq

  /**
   * Number of type variables used in the definition of this ADT
   */
  val typeArity: N = typeVariablesSeq.length.asInstanceOf[N]

  // ***************
  // * INJECTIVITY *
  // ***************

  /**
   * Theorem --- Injectivity of constructors.
   *
   *    Two instances of different construcors are always different.
   *
   * e.g. Nil != Cons(head, tail)
   */
  def injectivity(c1: SyntacticConstructor, c2: SyntacticConstructor) =
    require(c1.tag != c2.tag, "The given constructors must be different.")

    Lemma(!(c1.term1 === c2.term2)) {

      // STEP 0: Caching
      val tagTerm1: Term = c1.tagTerm
      val tagTerm2: Term = c2.tagTerm

      // STEP 1: Prove that the tags are different
      val diffTag = have(!(tagTerm1 === tagTerm2)) subproof {

        // STEP 1.1: Order the tags
        val minTag: Int = Math.min(c1.tag, c2.tag)
        val maxTag: Int = Math.max(c1.tag, c2.tag)

        val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Restate

        // STEP 1.2: Apply successor injectivity to both tags until one becomes 0
        (1 to minTag).foldLeft(start)((fact, i) =>
          val midMaxTag = toTerm(maxTag - i)
          val midMinTag = toTerm(minTag - i)
          have(successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag) by Cut(
            ADTThm.successorInjectivity of (n := midMaxTag, m := midMinTag),
            ADTThm.equivalenceApply of (p1 := successor(midMaxTag) === successor(midMinTag), p2 := midMaxTag === midMinTag)
          )
          have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
        )

        val chainInjectivity = thenHave(!(toTerm(maxTag - minTag) === emptySet) |- !(tagTerm1 === tagTerm2)) by Restate

        // STEP 1.3: Conclude using the fact that 0 is not the successor of any number
        have(!(toTerm(maxTag - minTag) === emptySet)) by Exact(ADTThm.zeroIsNotSucc)
        have(thesis) by Cut(lastStep, chainInjectivity)
      }

      // STEP 2: Prove that the terms are different if the tags are different
      have(c1.term1 === c2.term2 |- (tagTerm1 === tagTerm2) /\ (c1.subterm1 === c2.subterm2)) by Apply(ADTThm.equivalenceRevApply).on(
        pairExtensionality of (a := tagTerm1, b := c1.subterm1, c := tagTerm2, d := c2.subterm2)
      )
      thenHave(!(tagTerm1 === tagTerm2) |- !(c1.term1 === c2.term2)) by Weakening

      // STEP 3: Conclude
      have(!(c1.term1 === c2.term2)) by Cut(diffTag, lastStep)
    }

  // *************************
  // * INTRODUCTION FUNCTION *
  // *************************

  /**
   * Formula describing whether the variables of a constructor belongs to their respective domain or s when they are self-referencing.
   *
   * @param c The considered constructor
   * @param s The set of elements in which self-referencing variables of the constructor are.
   */
  private def constructorVarsInDomain(c: SyntacticConstructor, s: Term): Formula = wellTypedFormula(c.signature)(s)

  /**
   * Formula describing whether an element x is an instance of a specific constructor.
   *
   * @param c The constructor we want to check if x is an instance of
   * @param x The element we want to check if it is an instance of c
   * @param s The set of elements in which self-referencing arguments of the constructor are.
   */
  private def isConstructor(c: SyntacticConstructor, x: Term, s: Term): Formula =
    existsSeq(c.variables2, wellTypedFormula(c.signature2)(s) /\ (x === c.term2))

  /**
   * Formula describing whether an element x is an instance of one of this ADT's constructors.
   *
   * @param x The element we want to check if it is an instance of some constructor.
   * @param s The set of elements in which self-referencing arguments of the constructor are.
   */
  private def isConstructor(x: Term, s: Term): Formula = \/(constructors.map(c => isConstructor(c, x, s)))

  /**
   * The introduction (class) function applies this ADT's constructors to the argument to given to it.
   * It then adds to elements of the resulting set to the one given in argument. For example, if all arguments of the
   * constructors were self-referencing we would have:
   *
   *    introductionFunction(s) = {y | y = c(x1, ..., xn) for some c ∈ constructors and x1, ..., xn ∈ s} ∪ s
   *
   * In order to avoid introducing a new symbol in the theory, we describe this function with a predicate.
   *
   * @param s the argument of this function, i.e. set of elements on which the constructors are applied
   * @param y the element we want to check if it is in the image of s under the introduction function.
   *
   * @return a formula describing whether y ∈ introductionFunction(s)
   *
   * @note The existence of the image of the introduction function is guaranteed by the union and replacement axioms. Moreover, it is not necessary to compute the union with s. It however simplifies further proofs. See [[this.heightSuccessorStrong]] for a proof of the equivalence of the two definitions.
   */
  private def isInIntroductionFunctionImage(s: Term)(y: Term): Formula = isConstructor(y, s) \/ in(y, s)


  /**
   * Lemma --- The introduction function is monotonic with respect to set inclusion.
   *
   *      `s ⊆ t |- introductionFunction(s) ⊆ introductionFunction(t)`
   */
  private val introductionFunctionMononotic = Lemma(subset(s, t) |- isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(t)(x)) {
    // In the rest of the proof we assume that s ⊆ t

    // STEP 0: Caching predicates that are often used
    val subsetST = subset(s, t)
    val isConstructorXS = isConstructor(x, s)
    val isConstructorXT = isConstructor(x, t)

    // STEP 1: Prove x ∈ s implies x ∈ t
    have(subsetST |- forall(z, in(z, s) ==> in(z, t))) by Apply(ADTThm.equivalenceApply of (p1 := subsetST)).on(subsetAxiom.asInstanceOf)
    val subsetElimination = thenHave(subsetST |- in(z, s) ==> in(z, t)) by InstantiateForall(z)

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

        if c.arity == 0 then have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
        else
          // STEP 2.1: Prove that we can expand the domain of the (quantified) variables of the constructor
          val andSeq =
            for (v, ty) <- c.signature2 yield have((subsetST, varsWellTypedS) |- in(v, ty.getOrElse(t))) by Weakening(subsetElimination of (z := v))
          val expandingDomain = have((subsetST, varsWellTypedS) |- varsWellTypedT) by RightAnd(andSeq*)
          val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
          have((subsetST, varsWellTypedS, labelEq) |- varsWellTypedT /\ labelEq) by RightAnd(expandingDomain, weakeningLabelEq)

          // STEP 2.2: Prove that x stays an instance of this constructor if we expand the domain of the variables
          thenHave((subsetST, varsWellTypedS, labelEq) |- isConstructorCXT) by QuantifiersIntro(c.variables2)
          thenHave((subsetST, varsWellTypedS /\ labelEq) |- isConstructorCXT) by LeftAnd
          thenHave((subsetST, isConstructorCXS) |- isConstructorCXT) by QuantifiersIntro(c.variables2)

          // STEP 2.3: Weaken the conclusion to some constructor instead of a specific one
          thenHave((subsetST, isConstructorCXS) |- isConstructorXT) by Weakening

    // STEP 3: Prove that this holds for any constructor
    // ? Steps 2 and 3 can be merged and optimized through the repeated use of an external theorem like [[ADTHelperTheorems.unionPreimageMonotonic]]
    if constructors.isEmpty then have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
    else have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(isConstructorXSImpliesT*)

    // STEP 4: Prove the thesis by showing that making the union with the function argument does not change the monotonicity
    thenHave(subsetST |- isConstructorXS ==> isConstructorXT) by RightImplies
    have(thesis) by Cut(lastStep, ADTThm.unionPreimageMonotonic of (P := lambda(s, isConstructorXS)))
  }


  /**
   * Lemma --- Every constructor is in the image of the introduction function.
   *
   *      `For every c ∈ constructors, xi ∈ s, ..., xj ∈ s |- c(x1, ..., xn) ∈ introductionFunction(s)`
   */
  private val constructorIsInIntroductionFunction = constructors
    .map(c =>
      // Caching
      val constructorVarsInDomainCS = constructorVarsInDomain(c, s)

      c -> Lemma(constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)) {

        have(constructorVarsInDomainCS |- constructorVarsInDomainCS /\ (c.term === c.term)) by Restate

        // Replace each variable on the LHS of the equality by a quantified variable and then introduce an existential quantifier
        (c.variables2).foldRight((c.variables1, List[Variable]()))((v, acc) =>

          // At each step remove a variable and add a quantified one
          val oldVariables = acc._1.init
          val newVariables = v :: acc._2
          val vars = oldVariables ++ newVariables

          thenHave(constructorVarsInDomainCS |- existsSeq(newVariables, wellTypedFormula(vars.zip(c.specification))(s) /\ (c.term(vars) === c.term))) by RightExists

          (oldVariables, newVariables)
        )

        thenHave(constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)) by Weakening
      }
    )
    .toMap

  // **********************************
  // * EXTENDED INTRODUCTION FUNCTION *
  // **********************************

  /**
   * The extended introduction (class) function takes a function f as an argument instead of set.
   * - If f is not empty, it calls the introduction function on the union of the ranges of the function. Since f will
   * always be cumulative by assumption, this is equivalent as passing as argument the broadest set among the ranges of f.
   * - If the function is empty, it returns the empty set.
   *
   * This class function is in a suited format to be used within the transfinite recursion theorem, which will be called to
   * construct the height function.
   *
   * @see [[this.heightFunctionUniqueness]]
   *
   * @param f the function given as argument to the extended introduction function
   * @param x the element we want to check if it is in the image of f under the extended introduction function
   * @return a formula describing whether x ∈ extendedIntroductionFunction(f)
   */
  private def isInExtendedIntroductionFunctionImage(f: Term)(x: Term): Formula = !(f === emptySet) /\ isInIntroductionFunctionImage(unionRange(f))(x)

  /**
   * Lemma --- The extended introduction function is monotonic with respect to set inclusion.
   *
   *      `f ⊆ g |- extendedIntroductionFunction(f) ⊆ extendedIntroductionFunction(g)`
   */
  private val extendedIntroductionFunctionMonotonic = Lemma(subset(f, g) |- isInExtendedIntroductionFunctionImage(f)(x) ==> isInExtendedIntroductionFunctionImage(g)(x)) {

    // STEP 0: Caching
    val introFunUnionRangeF = isInIntroductionFunctionImage(unionRange(f))(x)
    val introFunUnionRangeG = isInIntroductionFunctionImage(unionRange(g))(x)

    // STEP 1: Instantiate monotonicity of the introduction function for the union of the ranges of f and g
    have(subset(f, g) |- introFunUnionRangeF ==> introFunUnionRangeG) by Cut(
      ADTThm.unionRangeMonotonic,
      introductionFunctionMononotic of (s := unionRange(f), t := unionRange(g))
    )
    val left = thenHave((subset(f, g), introFunUnionRangeF) |- introFunUnionRangeG) by Restate

    // STEP 2: Conclude by applying the conjuction on both sides
    have((subset(f, g), !(f === emptySet), introFunUnionRangeF) |- isInExtendedIntroductionFunctionImage(g)(x)) by RightAnd(left, ADTThm.subsetNotEmpty of (x := f, y := g))
  }

  // *******************
  // * HEIGHT FUNCTION *
  // *******************

  /**
   * The height function assigns to each natural number the set of elements of the ADT of that height or below.
   * The set of terms with height 0 is empty. Non inductive constructors have height one.
   * The height of an instance of an inductive constructor is the maximum height of its arguments plus one.
   * The height function is guaranteed to exists and is unique.
   *
   * @see [[this.heightFunctionUniqueness]]
   *
   * @param g the function we want to know if it is the height function
   *
   * @return a formula that is true if and only if g is the height function
   */
  private def isTheHeightFunction(h: Term): Formula =
    functional(h) /\ (relationDomain(h) === N) /\ forall(n, in(n, N) ==> forall(x, in(x, app(h, n)) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)))

  // Caching
  private val fIsTheHeightFunction: Formula = isTheHeightFunction(f)
  private val hIsTheHeightFunction: Formula = isTheHeightFunction(h)

  /**
   * Lemma --- There exists a unique height function for this ADT.
   *
   *     `∃!h. h = height`
   *
   * TODO: Prove this using transfinite recursion
   */
  private val heightFunUniqueness = Axiom(existsOne(h, hIsTheHeightFunction))

  /**
   * Lemma --- The height function exists.
   *
   *     `∃h. h = height`
   */
  private val heightFunctionExistence = Lemma(exists(h, hIsTheHeightFunction)) {
    have(thesis) by Apply(lisa.maths.Quantifiers.existsOneImpliesExists of (P := lambda(h, hIsTheHeightFunction))).on(heightFunUniqueness.asInstanceOf)
  }

  /**
   * Lemma --- If two functions are the height function then they are the same.
   *
   *     `f = height /\ h = height => f = h`
   */
  private val heightFunctionUniqueness2 = Lemma((fIsTheHeightFunction, hIsTheHeightFunction) |- f === h) {
    have(thesis) by Cut(heightFunUniqueness, ADTThm.existsOneUniqueness of (P := lambda(h, hIsTheHeightFunction), x := f, y := h))
  }

  /**
   * Lemma --- The height function is not empty.
   *
   *     `height ≠ ∅`
   */
  private val heightFunctionNonEmpty = Lemma(hIsTheHeightFunction |- !(h === emptySet)) {
    // The proof goes by contradiction. If the height function is empty then its domain is empty as well.
    // This would imply that the set of natural numbers is empty, which is a contradiction.
    have(N === emptySet |- ()) by Restate.from(ADTThm.natNotEmpty)
    thenHave((relationDomain(h) === emptySet, relationDomain(h) === N, relationDomain(h) === relationDomain(h)) |- ()) by LeftSubstEq.withParametersSimple(
      List((relationDomain(h), emptySet), (relationDomain(h), N)),
      lambda((x, y), y === x)
    )
    thenHave((relationDomain(h) === N, relationDomain(h) === relationDomain(h)) |- !(relationDomain(h) === emptySet)) by RightNot
    have(thesis) by Apply(ADTThm.nonEmptyDomain).on(lastStep)
  }

  /**
   * Lemma --- The set of elements of height n or below is the image of the extended introduction function under the height
   * function restricted to n (consequence of transfinite recursion).
   *
   *     `height(n) = extendedIntroductionFunction(height | n)`
   */
  private val heightApplication = Lemma((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, n)) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)) {

    // Caching
    val extendedIntroFunRestrictedFunM = isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)
    val heightFunApplicationDef = forall(n, in(n, N) ==> forall(x, in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM))

    // Nothing fancy, just instantiations and restates
    have(heightFunApplicationDef |- heightFunApplicationDef) by Hypothesis
    thenHave(heightFunApplicationDef |- in(n, N) ==> forall(x, in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM)) by InstantiateForall(n)
    thenHave((heightFunApplicationDef, in(n, N)) |- forall(x, in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM)) by Restate
    thenHave((heightFunApplicationDef, in(n, N)) |- in(x, app(h, n)) <=> extendedIntroFunRestrictedFunM) by InstantiateForall(x)
    thenHave(thesis) by Weakening
  }

  /**
   * Lemma --- The height function is monotonic
   *
   *     `n <= m => height(n) ⊆ height(m)`
   *
   * TODO: Try to pull out
   */
  private val heightMonotonic = Lemma((hIsTheHeightFunction, in(n, N), subset(m, n)) |- subset(app(h, m), app(h, n))) {

    // STEP 0: Caching
    val extendedIntroFunRestrictedFunM = isInExtendedIntroductionFunctionImage(restrictedFunction(h, m))(x)

    // STEP 1: Unfold the definition of height(m)
    have((hIsTheHeightFunction, in(n, N), subset(m, n)) |- in(x, app(h, m)) <=> extendedIntroFunRestrictedFunM) by Apply(heightApplication).on(ADTThm.subsetIsNat.asInstanceOf)
    val unfoldHeightApplicationM = have((hIsTheHeightFunction, in(n, N), subset(m, n), in(x, app(h, m))) |- extendedIntroFunRestrictedFunM) by Cut(
      lastStep,
      ADTThm.equivalenceRevApply of (p1 := in(x, app(h, m)), p2 := extendedIntroFunRestrictedFunM)
    )

    // STEP 2: Use the monotonicity of the extended introduction function
    have(subset(m, n) |- extendedIntroFunRestrictedFunM ==> isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)) by Cut(
      ADTThm.restrictedFunctionDomainMonotonic of (x := m, y := n, f := h),
      extendedIntroductionFunctionMonotonic of (f := restrictedFunction(h, m), g := restrictedFunction(h, n))
    )
    have((hIsTheHeightFunction, in(n, N), subset(m, n), extendedIntroFunRestrictedFunM) |- in(x, app(h, n))) by Apply(ADTThm.equivalenceRevApply).on(lastStep, heightApplication.asInstanceOf)

    // STEP 3: Fold the definition of subset
    have((hIsTheHeightFunction, in(n, N), subset(m, n), in(x, app(h, m))) |- in(x, app(h, n))) by Cut(unfoldHeightApplicationM, lastStep)
    thenHave((hIsTheHeightFunction, in(n, N), subset(m, n)) |- in(x, app(h, m)) ==> in(x, app(h, n))) by RightImplies
    thenHave((hIsTheHeightFunction, in(n, N), subset(m, n)) |- forall(x, in(x, app(h, m)) ==> in(x, app(h, n)))) by RightForall
    have(thesis) by Apply(ADTThm.equivalenceRevApply).on(lastStep, subsetAxiom.asInstanceOf)
  }

  /**
   * Lemma --- There is no element of height 0 in the ADT.
   *
   *     `!∃x ∈ adt. height(x) = 0`
   */
  private val heightZero = Lemma(hIsTheHeightFunction |- !in(x, app(h, emptySet))) {

    // This is due to the fact that the extended introduction function is the empty set when the function is empty
    // (which happens when the height is set to 0).
    have(hIsTheHeightFunction |- in(x, app(h, emptySet)) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, emptySet))(x)) by Cut(ADTThm.zeroIsNat, heightApplication of (n := emptySet))
    thenHave((restrictedFunction(h, emptySet) === emptySet, hIsTheHeightFunction) |- !in(x, app(h, emptySet))) by
      RightSubstEq.withParametersSimple(
        List((restrictedFunction(h, emptySet), emptySet)),
        lambda(s, in(x, app(h, emptySet)) <=> isInExtendedIntroductionFunctionImage(s)(x))
      )
    have(thesis) by Cut(ADTThm.restrictedFunctionEmptyDomain, lastStep)
  }

  /**
   * Lemma --- The set of elements of height n + 1 is the set of elements of height n to which the introduction function is applied.
   *
   *     `height(n + 1) = introductionFunction(height(n))`
   */
  private val heightSuccessorWeak = Lemma((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) {

    // STEP 1: Prove that the restriction of height to n + 1 is not empty
    val restrHeightNotEmpty: Formula = !(restrictedFunction(h, successor(n)) === emptySet)
    have(!(h === emptySet) |- restrHeightNotEmpty) by Cut(ADTThm.zeroIsNotSucc, ADTThm.restrictedFunctionNotEmpty of (d := successor(n)))
    val restrHeightNotEmptyLemma = have(hIsTheHeightFunction |- restrHeightNotEmpty) by Cut(heightFunctionNonEmpty, lastStep)

    // STEP 2: Use the fact that if the function is cumulative then ∪ range(height | n + 1) = height(n) to conclude the proof
    have((hIsTheHeightFunction, in(n, N)) |- subset(m, n) ==> subset(app(h, m), app(h, n))) by RightImplies(heightMonotonic)
    thenHave((hIsTheHeightFunction, in(n, N)) |- forall(m, subset(m, n) ==> subset(app(h, m), app(h, n)))) by RightForall
    val unionRangeRestr = have((hIsTheHeightFunction, in(n, N)) |- unionRange(restrictedFunction(h, successor(n))) === app(h, n)) by Apply(ADTThm.unionRangeCumulativeRestrictedFunction).on(lastStep)

    have((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, successor(n)))(x)) by Apply(heightApplication).on(
      ADTThm.equivalenceApply of (p1 := in(n, N)),
      ADTThm.successorIsNat.asInstanceOf
    )

    thenHave(
      (hIsTheHeightFunction, in(n, N), unionRange(restrictedFunction(h, successor(n))) === app(h, n)) |-
        in(x, app(h, successor(n))) <=> restrHeightNotEmpty /\ isInIntroductionFunctionImage(app(h, n))(x)
    ) by
      RightSubstEq.withParametersSimple(
        List((unionRange(restrictedFunction(h, successor(n))), app(h, n))),
        lambda(s, in(x, app(h, successor(n))) <=> (restrHeightNotEmpty /\ isInIntroductionFunctionImage(s)(x)))
      )

    have((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> restrHeightNotEmpty /\ isInIntroductionFunctionImage(app(h, n))(x)) by Cut(unionRangeRestr, lastStep)

    have((hIsTheHeightFunction, in(n, N), restrHeightNotEmpty) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by Apply(ADTThm.equivalenceAnd of (p2 := restrHeightNotEmpty))
      .on(lastStep)

    have(thesis) by Cut(restrHeightNotEmptyLemma, lastStep)
  }

  // ********
  // * TERM *
  // ********

  /**
   * Formula describing this ADT's term, i.e. the set of all its instances.
   * It equal to the union of all the terms that have a height.
   *
   *   `adt = ∪ height(n) = {x | ∃n ∈ N. x ∈ height(n)}`
   *
   * @param adt the set chracterizing this ADT
   */
  private def termDefinition(adt: Term): Formula = forall(t, in(t, adt) <=> forall(h, hIsTheHeightFunction ==> in(t, unionRange(h))))

  /**
   * Lemma --- There exists a unique set satisfying the definition of this ADT
   *
   *     `∃!z. z = ADT
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
      thenHave((f === h, inUnionRangeF) |- in(t, unionRange(h))) by RightSubstEq.withParametersSimple(
        List((f, h)),
        lambda(f, inUnionRangeF)
      )
      have((fIsTheHeightFunction, hIsTheHeightFunction, inUnionRangeF) |- in(t, unionRange(h))) by Cut(heightFunctionUniqueness2, lastStep)
      thenHave((fIsTheHeightFunction, inUnionRangeF) |- hIsTheHeightFunction ==> in(t, unionRange(h))) by RightImplies
      thenHave((fIsTheHeightFunction, inUnionRangeF) |- termDefinitionRight) by RightForall
      val forward = thenHave(fIsTheHeightFunction |- inUnionRangeF ==> termDefinitionRight) by RightImplies

      // STEP 1.2: Prove the backward implication of the definition
      have(termDefinitionRight |- termDefinitionRight) by Hypothesis
      thenHave(termDefinitionRight |- fIsTheHeightFunction ==> inUnionRangeF) by InstantiateForall(f)
      val backward = thenHave(fIsTheHeightFunction |- termDefinitionRight ==> inUnionRangeF) by Restate

      // STEP 1.3: Use the existence of the height function to prove the existence of this ADT
      have(fIsTheHeightFunction |- inUnionRangeF <=> termDefinitionRight) by RightIff(forward, backward)
      thenHave(fIsTheHeightFunction |- forall(t, inUnionRangeF <=> termDefinitionRight)) by RightForall

      thenHave(fIsTheHeightFunction |- exists(z, forall(t, in(t, z) <=> termDefinitionRight))) by RightExists
      thenHave(exists(f, fIsTheHeightFunction) |- exists(z, forall(t, in(t, z) <=> termDefinitionRight))) by LeftExists
      have(thesis) by Cut(heightFunctionExistence, lastStep)
    }

    // STEP 2: Conclude using the extension by definition

    have(thesis) by Cut(lastStep, uniqueByExtension of (schemPred := lambda(t, termDefinitionRight)))
  }

  /**
   * Class function defining the ADT. Takes as parameters the type variables of the ADT and return the set of all its instances.
   */
  val polymorphicTerm = FunctionDefinition[N](name, line.value, file.value)(typeVariablesSeq, z, termDefinition(z), termExistence).label

  /**
   * The set of all instances of the ADT where the type variables are not instantiated (i.e. are kept variable).
   */
  val term = polymorphicTerm.applySeq(typeVariablesSeq)

  /**
   * Definition of this ADT's term.
   */
  private val termDefinition: Formula = termDefinition(term)

  /**
   * Lemma --- This ADT satisfies its definition.
   *
   *     `adt = ∪ height(n)`
   */
  private val termSatisfiesDefinition = Lemma(termDefinition) {
    have(thesis) by InstantiateForall(term)(polymorphicTerm.definition)
  }

  // *************************
  // * TYPING / INTRODUCTION *
  // *************************

  /**
   * Lemma --- Every element of this ADT has a height. Conversely, if an element has a height, it is in this ADT.
   *
   *     ` x ∈ ADT <=> ∃n ∈ N. x ∈ height(n)`
   *
   * TODO: Split into two lemmas
   */
  private val termHasHeight = Lemma(hIsTheHeightFunction |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) {

    // STEP 0 : Instantiate the definition of this ADT and recover the forward and backward implications
    val termDefinition = have(in(x, term) <=> forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))) by InstantiateForall(x)(termSatisfiesDefinition)
    val termDefinitionForward = have(in(x, term) |- forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))) by Cut(
      termDefinition,
      ADTThm.equivalenceApply of (p1 := in(x, term), p2 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))))
    )
    val termDefinitionBackward = have(forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- in(x, term)) by Cut(
      termDefinition,
      ADTThm.equivalenceRevApply of (p2 := in(x, term), p1 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))))
    )

    // STEP 1 : Prove that an element is in this ADT if and only if it is in one of the images of the height function.
    have(hIsTheHeightFunction |- in(x, term) <=> in(x, unionRange(h))) subproof {

      // STEP 1.1 : Forward implication
      have(forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))) by Hypothesis
      thenHave(forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- hIsTheHeightFunction ==> in(x, unionRange(h))) by InstantiateForall(h)
      thenHave((forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))), hIsTheHeightFunction) |- in(x, unionRange(h))) by Restate

      val forward = have(hIsTheHeightFunction |- in(x, term) ==> in(x, unionRange(h))) by Apply(lastStep).on(termDefinitionForward)

      // STEP 1.2 : Backward implication, follows from uniqueness of the height function
      have(in(x, unionRange(h)) |- in(x, unionRange(h))) by Hypothesis
      thenHave((f === h, in(x, unionRange(h))) |- in(x, unionRange(f))) by RightSubstEq.withParametersSimple(List((f, h)), lambda(h, in(x, unionRange(h))))
      have((fIsTheHeightFunction, hIsTheHeightFunction, in(x, unionRange(h))) |- in(x, unionRange(f))) by Cut(heightFunctionUniqueness2, lastStep)
      thenHave((hIsTheHeightFunction, in(x, unionRange(h))) |- fIsTheHeightFunction ==> in(x, unionRange(f))) by RightImplies
      thenHave((hIsTheHeightFunction, in(x, unionRange(h))) |- forall(f, fIsTheHeightFunction ==> in(x, unionRange(f)))) by RightForall
      have((hIsTheHeightFunction, in(x, unionRange(h))) |- in(x, term)) by Cut(lastStep, termDefinitionBackward)
      val backward = thenHave(hIsTheHeightFunction |- in(x, unionRange(h)) ==> in(x, term)) by RightImplies

      have(thesis) by RightIff(forward, backward)
    }

    // STEP 2: Conclude by instantiating the union range membership lemma
    have(hIsTheHeightFunction |- in(x, term) <=> ∃(n, in(n, relationDomain(h)) /\ in(x, app(h, n)))) by Apply(ADTThm.equivalenceRewriting).on(ADTThm.unionRangeMembership.asInstanceOf, lastStep)

    thenHave((hIsTheHeightFunction, relationDomain(h) === N) |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) by RightSubstEq.withParametersSimple(
      List((relationDomain(h), N)),
      lambda(z, in(x, term) <=> ∃(n, in(n, z) /\ in(x, app(h, n))))
    )
  }

  /**
   * Lemma --- Every element of this ADT has a height. Conversely, if an element has a height, it is in this ADT.
   *
   *     ` xi, ..., xj ∈ ADT <=> ∃n ∈ N. xi, ..., xj ∈ height(n)`
   *
   * TODO: Work this out
   * TODO: Split into two lemmas
   */
  private val termsHaveHeight = constructors
    .map(c =>
      c -> Lemma(hIsTheHeightFunction |- (constructorVarsInDomain(c, term) <=> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))) {

        if c.variables.isEmpty then have(thesis) by Weakening(ADTThm.existsNat)
        else

          // STEP 1: Backward implication

          val backward = have(hIsTheHeightFunction |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) ==> constructorVarsInDomain(c, term)) subproof {
            val andSeq = for (v, ty) <- c.signature yield ty match
              case Self =>
                val termHasHeightBackward = have((hIsTheHeightFunction, exists(n, in(n, N) /\ in(v, app(h, n)))) |- in(v, term)) by Cut(
                  termHasHeight of (x := v),
                  ADTThm.equivalenceRevApply of (p1 := ∃(n, in(n, N) /\ in(v, app(h, n))), p2 := in(v, term))
                )

                have((in(n, N) /\ in(v, app(h, n))) |- in(n, N) /\ in(v, app(h, n))) by Restate
                thenHave((in(n, N) /\ in(v, app(h, n))) |- exists(n, in(n, N) /\ in(v, app(h, n)))) by RightExists
                have((hIsTheHeightFunction, in(n, N) /\ in(v, app(h, n))) |- in(v, term)) by Cut(lastStep, termHasHeightBackward)
                thenHave((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, term)) by Weakening
              case GroundType(t) =>
                have((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, t)) by Restate

            have((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by RightAnd(andSeq*)
            thenHave((hIsTheHeightFunction, exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- constructorVarsInDomain(c, term)) by LeftExists
          }

          // STEP 2: Forward implication

          val forward = have(hIsTheHeightFunction |- constructorVarsInDomain(c, term) ==> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) subproof {
            val nSeq: Seq[Variable] = (0 until c.variables.size).map(i => Variable(s"n$i"))
            val max = if c.arity == 0 then emptySet else nSeq.reduce[Term](setUnion(_, _))

            val maxInN = have(/\(nSeq.map(n => in(n, N))) |- in(max, N)) by Sorry

            val andSeq = for ((v, ty), ni) <- c.signature.zip(nSeq) yield
              val niInMax = have(subset(ni, max)) by Sorry

              ty match
                case Self =>
                  have((hIsTheHeightFunction, in(max, N), subset(ni, max)) |- subset(app(h, ni), app(h, max))) by Restate.from(heightMonotonic of (m := ni, n := max))
                  have((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- subset(app(h, ni), app(h, max))) by Sorry // Apply(lastStep).on(Seq(maxInN, niInMax), excluding = nSeq)
                  have((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- forall(z, in(z, app(h, ni)) ==> in(z, app(h, max)))) by Apply(ADTThm.equivalenceApply)
                    .on(Seq(lastStep, subsetAxiom), excluding = nSeq)
                  thenHave((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- in(v, app(h, ni)) ==> in(v, app(h, max))) by InstantiateForall(v)
                  thenHave((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N))), in(v, app(h, ni))) |- in(v, app(h, max))) by Restate
                case GroundType(t) =>
                  have((/\(nSeq.map(n => in(n, N))), hIsTheHeightFunction, in(v, t)) |- in(v, t)) by Restate

              have((/\(nSeq.map(n => in(n, N))), hIsTheHeightFunction, in(v, ty.getOrElse(app(h, ni)))) |- in(max, N) /\ in(v, ty.getOrElse(app(h, max)))) by RightAnd(maxInN, lastStep)
              thenHave(nSeq.map(n => in(n, N) /\ in(v, ty.getOrElse(app(h, n)))).toSet + hIsTheHeightFunction |- in(max, N) /\ in(v, ty.getOrElse(app(h, max)))) by Weakening
              thenHave(nSeq.map(n => in(n, N) /\ in(v, ty.getOrElse(app(h, n)))).toSet + hIsTheHeightFunction |- ∃(n, in(n, N) /\ in(v, ty.getOrElse(app(h, n))))) by RightExists

            sorry
          }

          // STEP 3: Conclude
          have(thesis) by RightIff(forward, backward)
      }
    )
    .toMap

  /**
   * Lemma --- If all inductive arguments of a constructor have height below n then the instance of
   * this constructor has height below n + 1.
   *
   *      ` xi, ..., xj ∈ height(n) |- c(x1, ..., xn) ∈ height(n + 1)`
   */
  private val heightConstructor = constructors
    .map(c =>
      c -> Lemma((hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, app(h, successor(n)))) {

        // Caching
        val constructorInIntroFunHeight = isInIntroductionFunctionImage(app(h, n))(c.term)

        // Chaining the lemma on the elements of height n + 1 and the one on constructors being in the image of the introduction function
        have((hIsTheHeightFunction, in(n, N), constructorInIntroFunHeight) |- in(c.term, app(h, successor(n)))) by Cut(
          heightSuccessorWeak of (x := c.term),
          ADTThm.equivalenceRevApply of (p1 := constructorInIntroFunHeight, p2 := in(c.term, app(h, successor(n))))
        )
        have((hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, app(h, successor(n)))) by Cut(constructorIsInIntroductionFunction(c) of (s := app(h, n)), lastStep)
      }
    )
    .toMap

  /**
   * Lemma --- If all inductive arguments of a constructor are in this ADT, and the non inductive ones in their respective domain,
   * then the instance of this constructor is in this ADT as well. Also known as introduction rules.
   *
   *      ` xi, ..., xj ∈ ADT |- c(x1, ..., xn) ∈ ADT`
   */
  val intro = constructors
    .map(c => {
      c ->
        Lemma(simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))) {
          // STEP 0: Instantiate the forward direction of termsHaveHeight.
          val termsHaveHeightForward = have((hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by Cut(
            termsHaveHeight(c),
            ADTThm.equivalenceApply of (p1 := constructorVarsInDomain(c, term), p2 := exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))
          )

          // STEP 1: Prove that if an instance of a constructor has height n + 1 then it is in this ADT.
          val left = have(in(n, N) |- in(successor(n), N)) by Cut(ADTThm.successorIsNat, ADTThm.equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N)))
          val right = have(in(c.term, app(h, successor(n))) |- in(c.term, app(h, successor(n)))) by Hypothesis
          have((in(n, N), in(c.term, app(h, successor(n)))) |- in(successor(n), N) /\ in(c.term, app(h, successor(n)))) by RightAnd(left, right)
          thenHave((in(n, N), in(c.term, app(h, successor(n)))) |- exists(m, in(m, N) /\ in(c.term, app(h, m)))) by RightExists
          have((hIsTheHeightFunction, in(n, N), in(c.term, app(h, successor(n)))) |- in(c.term, term)) by Apply(ADTThm.equivalenceRevApply).on(lastStep, termHasHeight.asInstanceOf)

          // STEP 2: Prove that if the inductive arguments of the constructor have height then the instance of the constructor is in the ADT.
          have((hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, term)) by Cut(heightConstructor(c), lastStep)

          // STEP 3: Prove that if the inductive arguments of the constructor are in the ADT then they have a height and therefore
          // the instance of the constructor is in the ADT.
          thenHave((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(c.term, term)) by LeftAnd
          thenHave((hIsTheHeightFunction, exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- in(c.term, term)) by LeftExists
          have((hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- in(c.term, term)) by Cut(termsHaveHeightForward, lastStep)

          // STEP 4: Remove lingering assumptions
          thenHave((exists(h, hIsTheHeightFunction), constructorVarsInDomain(c, term)) |- in(c.term, term)) by LeftExists
          have(constructorVarsInDomain(c, term) |- in(c.term, term)) by Cut(heightFunctionExistence, lastStep)
        }
    })
    .toMap

  // ************************
  // * STRUCTURAL INDUCTION *
  // ************************

  /**
   * Lemma --- An element has height n + 1 if and only if it is the instance of some constructor with inductive arguments of height n.
   *
   *    ` x ∈ height(n + 1) <=> x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n)`
   */
  private lazy val heightSuccessorStrong = Lemma((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isConstructor(x, app(h, n))) {
    val forward = have((hIsTheHeightFunction, in(n, N)) |- isInIntroductionFunctionImage(app(h, n))(x) ==> isConstructor(x, app(h, n))) subproof {

      def inductionFormula(n: Term): Formula = isInIntroductionFunctionImage(app(h, n))(x) ==> isConstructor(x, app(h, n))
      val inductionFormulaN: Formula = inductionFormula(n)
      val inductionFormulaSuccN: Formula = inductionFormula(successor(n))

      // STEP 1.1 : Base case
      val isContructorXHEmptySet = isConstructor(x, app(h, emptySet))
      val baseCaseLeft = have(isContructorXHEmptySet |- isContructorXHEmptySet) by Hypothesis
      val baseCaseRight = have((hIsTheHeightFunction, in(x, app(h, emptySet))) |- ()) by Restate.from(heightZero)
      have((hIsTheHeightFunction, isInIntroductionFunctionImage(app(h, emptySet))(x)) |- isContructorXHEmptySet) by LeftOr(baseCaseLeft, baseCaseRight)
      thenHave(hIsTheHeightFunction |- isInIntroductionFunctionImage(app(h, emptySet))(x) ==> isContructorXHEmptySet) by RightImplies
      val inductiveCaseRemaining = have((hIsTheHeightFunction, forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))) |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(
        lastStep,
        ADTThm.natInduction of (P := lambda(n, inductionFormulaN))
      )

      // STEP 1.2: Unfolding the definition of subset
      have(subset(app(h, n), app(h, successor(n))) |- forall(z, in(z, app(h, n)) ==> in(z, app(h, successor(n))))) by Cut(
        subsetAxiom of (x := app(h, n), y := app(h, successor(n))),
        ADTThm.equivalenceApply of (p1 := subset(app(h, n), app(h, successor(n))), p2 := forall(z, in(z, app(h, n)) ==> in(z, app(h, successor(n)))))
      )
      val subsetElimination = thenHave(subset(app(h, n), app(h, successor(n))) |- in(y, app(h, n)) ==> in(y, app(h, successor(n)))) by InstantiateForall(y)

      // STEP 1.3 : Use monotonicity to prove that y ∈ height(n) => y ∈ height(n + 1)
      have(in(n, N) |- in(successor(n), N)) by Cut(ADTThm.successorIsNat, ADTThm.equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N)))
      have((hIsTheHeightFunction, in(n, N), subset(n, successor(n))) |- subset(app(h, n), app(h, successor(n)))) by Cut(lastStep, heightMonotonic of (n := successor(n), m := n))
      have((hIsTheHeightFunction, in(n, N)) |- subset(app(h, n), app(h, successor(n)))) by Cut(ADTThm.subsetSuccessor, lastStep)
      val liftHeight = have((hIsTheHeightFunction, in(n, N)) |- in(y, app(h, n)) ==> in(y, app(h, successor(n)))) by Cut(lastStep, subsetElimination)

      // STEP 1.4 : Generalize the above result to show that if for some c, x = c(x1, ..., xn) with xi, ..., xj ∈ height(n)
      // then for some c', x = c'(x1, ..., xn) with xi, ..., xj ∈ height(n + 1).

      // Caching
      val isConstructorXHN = isConstructor(x, app(h, n))
      val isConstructorXHSuccN = isConstructor(x, app(h, successor(n)))
      val liftConstructorHeight =
        if constructors.size == 0 then have((hIsTheHeightFunction, in(n, N), isConstructorXHN) |- isConstructorXHSuccN) by Restate
        else
          val liftConstructorHeightOrSequence =
            for c <- constructors yield

              // Caching
              val isConstructorCXHN = isConstructor(c, x, app(h, n))
              val isConstructorCXHSuccN = isConstructor(c, x, app(h, successor(n)))
              val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
              val constructorVarsInHSuccN = constructorVarsInDomain(c, app(h, successor(n)))

              if c.arity == 0 then have((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorCXHSuccN) by Restate
              else
                val liftHeightAndSequence =
                  for (v, ty) <- c.signature
                  yield have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(v, ty.getOrElse(app(h, successor(n))))) by Weakening(liftHeight of (y := v))

                val left = have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- constructorVarsInHSuccN) by RightAnd(liftHeightAndSequence*)
                val right = have(x === c.term |- x === c.term) by Hypothesis

                have((hIsTheHeightFunction, in(n, N), constructorVarsInHN, (x === c.term)) |- constructorVarsInHSuccN /\ (x === c.term )) by RightAnd(
                  left,
                  right
                )
                thenHave((hIsTheHeightFunction, in(n, N), constructorVarsInHN /\ (x === c.term)) |- constructorVarsInHSuccN /\ (x === c.term)) by LeftAnd
                thenHave((hIsTheHeightFunction, in(n, N), constructorVarsInHN /\ (x === c.term)) |- isConstructorCXHSuccN) by QuantifiersIntro(c.variables)
                thenHave((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorCXHSuccN) by QuantifiersIntro(c.variables)

              thenHave((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorXHSuccN) by Weakening

          have((hIsTheHeightFunction, in(n, N), isConstructorXHN) |- isConstructorXHSuccN) by LeftOr(liftConstructorHeightOrSequence*)

      // STEP 1.5: Show that x ∈ introductionFunction(height(n + 1)) => for some c, x = c(x1, ..., xn)
      // with xi, ..., xj ∈ height(n + 1).
      val heightSuccessorWeakForward = have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n)))) |- isInIntroductionFunctionImage(app(h, n))(x)) by Cut(
        heightSuccessorWeak,
        ADTThm.equivalenceApply of (p1 := in(x, app(h, successor(n))), p2 := isInIntroductionFunctionImage(app(h, n))(x))
      )
      have((inductionFormulaN, isInIntroductionFunctionImage(app(h, n))(x)) |- isConstructorXHN) by Restate
      have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n))), inductionFormulaN) |- isConstructorXHN) by Cut(heightSuccessorWeakForward, lastStep)
      val right = have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n))), inductionFormulaN) |- isConstructorXHSuccN) by Cut(lastStep, liftConstructorHeight)
      val left = have(isConstructorXHSuccN |- isConstructorXHSuccN) by Hypothesis
      have((hIsTheHeightFunction, in(n, N), inductionFormulaN, isInIntroductionFunctionImage(app(h, successor(n)))(x)) |- isConstructorXHSuccN) by LeftOr(left, right)

      // STEP 1.6: Conclude
      thenHave((hIsTheHeightFunction, in(n, N), inductionFormulaN) |- inductionFormulaSuccN) by RightImplies
      thenHave((hIsTheHeightFunction, in(n, N)) |- inductionFormulaN ==> inductionFormulaSuccN) by RightImplies
      thenHave(hIsTheHeightFunction |- in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)) by RightImplies
      thenHave(hIsTheHeightFunction |- forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))) by RightForall
      have(hIsTheHeightFunction |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(lastStep, inductiveCaseRemaining)
      thenHave(hIsTheHeightFunction |- in(n, N) ==> inductionFormulaN) by InstantiateForall(n)
    }

    // STEP 2: Prove the backward implication
    val backward = have((hIsTheHeightFunction, in(n, N)) |- isConstructor(x, app(h, n)) ==> isInIntroductionFunctionImage(app(h, n))(x)) by Restate

    // STEP 3: Conclude
    have((hIsTheHeightFunction, in(n, N)) |- isInIntroductionFunctionImage(app(h, n))(x) <=> isConstructor(x, app(h, n))) by RightIff(forward, backward)
    have(thesis) by Apply(ADTThm.equivalenceRewriting).on(lastStep, heightSuccessorWeak.asInstanceOf)
  }

  /**
   * Generates the structural inductive case for a given constructor.
   *
   * @param c the constructor
   */
  lazy val inductiveCase: Map[SyntacticConstructor, Formula] = constructors
    .map(c =>
      c -> c.signature.foldRight[Formula](P(c.term))((el, fc) =>
        val (v, ty) = el
        ty match
          case Self => forall(v, in(v, term) ==> (P(v) ==> fc))
          case GroundType(t) => forall(v, in(v, t) ==> fc)
      )
    )
    .toMap

  /**
   * Lemma --- Structural induction principle for this ADT.
   *
   *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
   */
  lazy val induction = Lemma(constructors.foldRight[Formula](forall(x, in(x, term) ==> P(x)))((c, f) => inductiveCase(c) ==> f)) {

    // List of cases to prove for structural induction to hold
    val structuralInductionPreconditions: Formula = /\(constructors.map(inductiveCase))

    // We want to prove the claim by induction on the height of n, i.e. prove that for any
    // n in N, P holds.
    def inductionFormula(n: Term): Formula = forall(x, in(x, app(h, n)) ==> P(x))
    val inductionFormulaN: Formula = inductionFormula(n)

    // STEP 1: Prove the base case
    have(hIsTheHeightFunction |- in(x, app(h, emptySet)) ==> P(x)) by Weakening(heightZero)
    val zeroCase = thenHave(hIsTheHeightFunction |- inductionFormula(emptySet)) by RightForall

    val inductiveCaseRemaining = have((hIsTheHeightFunction, forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n))))) |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(
      zeroCase,
      ADTThm.natInduction of (P := lambda(n, inductionFormulaN))
    )

    // STEP 2: Prove the inductive case
    val succCase = have((hIsTheHeightFunction, structuralInductionPreconditions) |- forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n))))) subproof {

      // STEP 2.1 : Prove that if the x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n) then P(x) holds.
      val isConstructorImpliesP = have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(x, app(h, n))) |- P(x)) subproof {

        if constructors.isEmpty then have(thesis) by Restate
        else
          val orSeq =
            (for c <- constructors yield

              // Caching
              val constructorPrecondition = inductiveCase(c)
              val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
              val constructorVarsInHNEx = ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
              val constructorVarsInTerm = constructorVarsInDomain(c, term)

              // STEP 2.1.1: Prove that if xi, ..., xj ∈ height(n) then xi, ..., xj ∈ ADT.
              val constructorQuantVarsInHNToTerm = have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- constructorVarsInTerm) subproof {
                have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(n, N) /\ constructorVarsInHN) by Restate
                val consVarL = thenHave((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- constructorVarsInHNEx) by RightExists
                have((constructorVarsInTerm <=> constructorVarsInHNEx, constructorVarsInHNEx) |- constructorVarsInTerm) by Restate.from(
                  ADTThm.equivalenceRevApply of (p1 := constructorVarsInTerm, p2 := constructorVarsInHNEx)
                )
                have((hIsTheHeightFunction, constructorVarsInHNEx) |- constructorVarsInTerm) by Cut(
                  termsHaveHeight(c),
                  lastStep
                )
                have(thesis) by Cut(consVarL, lastStep)
              }


              // STEP 2.1.2: Prove that if xi, ..., xj ∈ height(n) then P(c(x1, ..., xn)).
              have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- constructorPrecondition) by Restate

              c.signature
                .foldLeft(lastStep)((fact, el) =>
                  val (v, ty) = el

                  fact.statement.right.head match
                    case Forall(_, factCclWithoutForall) =>
                      thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- factCclWithoutForall) by InstantiateForall(v)

                      factCclWithoutForall match
                        case Implies(membership, subformula) =>
                          ty match
                            case Self =>
                              subformula match
                                case Implies(hypothesis, subSubFormula) =>
                                  val proofSubSubFormula = thenHave(
                                    (hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInTerm, constructorVarsInHN, P(v)) |- subSubFormula
                                  ) by Weakening

                                  have(inductionFormulaN |- inductionFormulaN) by Hypothesis
                                  thenHave(inductionFormulaN |- in(v, app(h, n)) ==> P(v)) by InstantiateForall(v)
                                  thenHave((inductionFormulaN, constructorVarsInHN) |- P(v)) by Weakening

                                  have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInTerm, constructorVarsInHN) |- subSubFormula) by Cut(
                                    lastStep,
                                    proofSubSubFormula
                                  )
                                  have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- subSubFormula) by Cut(
                                    constructorQuantVarsInHNToTerm,
                                    lastStep
                                  )

                                case _ => throw UnreachableException

                            case GroundType(t) =>
                              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- subformula) by Restate
                        case _ => throw UnreachableException
                    case _ => throw UnreachableException
                )

              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- P(c.term)) by Restate

              // STEP 2.1.3: Prove that if xi, ..., xj ∈ height(n) then P(x).
              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN, x === c.term) |- P(x)) by RightSubstEq
                .withParametersSimple(List((x, c.term)), lambda(x, P(x)))

              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN /\ (x === c.term)) |- P(x)) by LeftAnd

              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, isConstructor(c, x, app(h, n))) |- P(x)) by QuantifiersIntro(c.variables)
              thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(c, x, app(h, n))) |- P(x)) by Weakening
            ).toSeq


          have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(x, app(h, n))) |- P(x)) by LeftOr(orSeq*)
      }

      // STEP 2.2: Prove that if x ∈ height(n + 1) then P(x) holds.
      have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n)))) |- isConstructor(x, app(h, n))) by Cut(
        heightSuccessorStrong,
        ADTThm.equivalenceApply of (p1 := in(x, app(h, successor(n))), p2 := isConstructor(x, app(h, n)))
      )
      have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, in(x, app(h, successor(n)))) |- P(x)) by Cut(lastStep, isConstructorImpliesP)

      // STEP 2.3: Conclude
      thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN) |- in(x, app(h, successor(n))) ==> P(x)) by RightImplies

      thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN) |- inductionFormula(successor(n))) by RightForall
      thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- inductionFormulaN ==> inductionFormula(successor(n))) by RightImplies
      thenHave((hIsTheHeightFunction, structuralInductionPreconditions) |- in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n)))) by RightImplies
      thenHave(thesis) by RightForall
    }

    // STEP 3: Conclude

    have((hIsTheHeightFunction, structuralInductionPreconditions) |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(lastStep, inductiveCaseRemaining)
    thenHave((hIsTheHeightFunction, structuralInductionPreconditions) |- in(n, N) ==> inductionFormulaN) by InstantiateForall(n)
    thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- inductionFormulaN) by Restate
    thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- in(x, app(h, n)) ==> P(x)) by InstantiateForall(x)
    thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N) /\ in(x, app(h, n))) |- P(x)) by Restate
    val exImpliesP = thenHave((hIsTheHeightFunction, structuralInductionPreconditions, exists(n, in(n, N) /\ in(x, app(h, n)))) |- P(x)) by LeftExists
    have((hIsTheHeightFunction, in(x, term)) |- exists(n, in(n, N) /\ in(x, app(h, n)))) by Cut(termHasHeight, ADTThm.equivalenceApply of (p1 := in(x, term), p2 := exists(n, in(n, N) /\ in(x, app(h, n)))))

    have((hIsTheHeightFunction, structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(lastStep, exImpliesP)
    thenHave((exists(h, hIsTheHeightFunction), structuralInductionPreconditions, in(x, term)) |- P(x)) by LeftExists
    have((structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(heightFunctionExistence, lastStep)
    thenHave(structuralInductionPreconditions |- in(x, term) ==> P(x)) by RightImplies
    thenHave(structuralInductionPreconditions |- forall(x, in(x, term) ==> P(x))) by RightForall
  }

}

/**
  * Semantic set theoretical interpretation of a constructor for an algebraic data type.
  * That is a function from the arguments' domains to the set of instances of the algebraic data type.
  * 
  *   `c : T1 -> ... -> Tn -> ADT`
  * 
  * Since polymorphism is supported, this function is parametrized by the type variables appearing inside
  * the specification of the ADT. In this sense, a constructor is a class function whose parameters are 
  * type variables and whose body is the set theoretic function detailed above. With polymorphism, the signature
  * thus becomes:
  * 
  *   `c(X1, ..., Xn) : T1(X1, ..., Xn) -> ... -> Tn(X1, ..., Xn) -> ADT(X1, ..., Xn)`
  * 
  * Injectivity and introduction rule are proven within this class.
  *
  * @constructor generates a class function for this constructor
  * @param line the line at which this constructor is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param file the file in which this constructor is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param name the name of this constructor
  * @param underlying the syntactic constructor
  * @param adt the algebraic data type to which this constructor belongs
  */
private class SemanticConstructor[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
  val name: String,
  val underlying: SyntacticConstructor,
  val adt: SyntacticADT[N],
) {
   /**
     * Full name of this constructor, i.e. concatenation of the ADT name and this constructor name.
     */
    val fullName: String = s"${adt.name}/${name}"

    /**
     * Type variables that may appear in the signature of this constructor.
     */
    val typeVariables: Variable ** N = adt.typeVariables

    /**
      * Sequence of type variables that may appear in the signature of this constructor.
      */
    val typeVariablesSeq: Seq[Variable] = adt.typeVariablesSeq

    /**
      * Number of type variables in the signature of this constructor.
      */
    val typeArity: N = adt.typeArity

    /**
     * Variables used for constructor arguments.
     */
    val variables: Seq[Variable] = underlying.variables

    /**
     * Variables used for constructor arguments.
     */
    val variables1: Seq[Variable] = underlying.variables1

    /**
     * Alternative set of variables used for constructor arguments.
     */
    val variables2: Seq[Variable] = underlying.variables2

    /**
     * Set of variables for this constructor with their respective domain or a 
     * special symbol in case the domain is the ADT.
     * 
     * @param vars variables
     */
    def syntacticSignature(vars: Seq[Variable]): Seq[(Variable, ConstructorArgument)] = 
      vars.zip(underlying.specification)

    /**
     * Variables of this constructor with their respective domain or a special symbol in case the domain is the ADT.
     */
    val syntacticSignature: Seq[(Variable, ConstructorArgument)] = underlying.signature

    /**
     * Constructor arguments with their respective domains.
     * 
     * @param vars this constructor arguments
     */
    def semanticSignature(vars: Seq[Variable]): Seq[(Variable, Term)] = vars.zip(underlying.specification.map(_.getOrElse(adt.term)))

    /**
     * Variables of this constructor with their respective domains.
     */
    val semanticSignature: Seq[(Variable, Term)] = semanticSignature(variables)

    /**
     * Variables of this constructor with their respective domains.
     */
    val semanticSignature1: Seq[(Variable, Term)] = semanticSignature

    /**
     * Alternative set of variables of this constructor with their respective domain.
     */
    val semanticSignature2: Seq[(Variable, Term)] = semanticSignature(variables2)

    /**
     * Type of this constructor.
     */
    val typ: Term = semanticSignature.unzip._2.foldRight[Term](adt.term)((a, b) => a |=> b)

    /**
     * Arity of this constructor.
     */
    val arity: Int = variables.size

    /**
     * Internal representation of this constructor (i.e. as a tuple).
     */
    val structuralTerm: Term = underlying.term
    /**
    * Internal representation of this constructor (i.e. as a tuple).
    */
    val structuralTerm1: Term = underlying.term1
    /**
    * Internal representation of this constructor (i.e. as a tuple) with an alternative set of variables.
    */
    val structuralTerm2: Term = underlying.term2

    /**
     * Definition of this constructor.
     *
     * Formally it is the only function whose codomain is the ADT such that for all variables x1 :: S1, ...,xn :: Sn
     * c * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...))
     */
    private val untypedDefinition = (c :: typ) /\ forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appSeq(c)(variables) === structuralTerm))

    /**
     * Lemma --- Uniqueness of this constructor.
     *
     *     ` ∃!c. c ∈ T1 -> ... -> Tn -> ADT /\ ∀x1, ..., xn. c * x1 * ...* xn = (tagc, (x1, (..., (xn, ∅)...))`
     */
    private val uniqueness = Axiom(existsOne(c, untypedDefinition))

    /**
     * Class function representing this constructor
     */
    private val classFunction = FunctionDefinition[N](fullName, line.value, file.value)(typeVariablesSeq, c, untypedDefinition, uniqueness).label

    /**
      * Identifier of this constructor.
      */
    val id: Identifier = classFunction.id

    /**
      * This constructor in which type variables are instantiated.
      *
      * @param args the instances of this constructor's type variables
      */
    def term(args: Seq[Term]): Term = classFunction.applySeq(args)

    /**
     * Constructor where type variables are instantiated with schematic variables.
     */
    private val term: Term = term(typeVariablesSeq)

    /**
     * Constructor where type variables are instantiated with schematic variables and arguments instantiated.
     * 
     * @param args the instances of this constructor arguments
     */
    def appliedTerm(args: Seq[Term]): Term = appSeq(term)(args)

    /**
     * Constructor where type variables and arguments are instantiated with schematic variables.
     */
    val appliedTerm: Term = appliedTerm(variables)

    /**
     * Constructor where type variables and arguments are instantiated with schematic variables.
     */
    val appliedTerm1: Term = appliedTerm

    /**
     * Constructor where type variables and arguments are instantiated with schematic variables.
     * Arguments variables are however drawn from an alternative set of variables.
     */
    val appliedTerm2: Term = appliedTerm(variables2)

    /**
     * Lemma --- This constructor is equal to its internal representation.
     *
     *     `∀x1, ..., xn. c * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...))`
     */
    val shortDefinition = Lemma(forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm))) {
      have(forall(c, (term === c) <=> untypedDefinition)) by Exact(classFunction.definition)
      thenHave((term === term) <=> ((term :: typ) /\ forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)))) by InstantiateForall(term)
      thenHave(thesis) by Weakening
    }

    /**
     * Lemma --- Introduction rule for this constructor.
     * 
     *    `∀A1, ..., Am. c(X1, ..., Xm) ∈ T1(X1, ..., Xm) -> ... -> Tn(X1, ..., Xm) -> ADT(X1, ..., Xm)`
     * 
     * where Ai are the type variables of the ADT and Ti are domains of this constructor arguments.
     * 
     * e.g. `∀T. nil(T) ∈ list(T)` and  `∀T. cons(T) ∈ T -> list(T) -> list(T)`
     */
    val intro = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
      have(forall(c, (term === c) <=> untypedDefinition)) by Exact(classFunction.definition)
      thenHave((term === term) <=> ((term :: typ) /\ forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)))) by InstantiateForall(term)
      thenHave(term :: typ) by Weakening
      thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
    }

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
     *
     * e.g. Cons(head1, tail1) === Cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
     */
    lazy val injectivity = 
      val vars1WellTyped: Set[Formula] = wellTypedSet(semanticSignature1)
      val vars2WellTyped: Set[Formula] = wellTypedSet(semanticSignature2)

      if arity == 0 then
        Lemma(appliedTerm1 === appliedTerm2) {
          have(thesis) by RightRefl
        }
      else
        Lemma(vars1WellTyped ++ vars2WellTyped |- simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))) {

          have(forallSeq(variables1, wellTypedFormula(semanticSignature1) ==> (appliedTerm1 === structuralTerm1))) by Restate.from(shortDefinition)

          variables1.foldLeft(lastStep)((fact, v) =>
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
                case _ => throw UnreachableException
            )
          val tappTerm1Def = thenHave(vars1WellTyped |- appliedTerm1 === structuralTerm1) by Restate

          // println(forallSeq(variables1, wellTypedFormula(semanticSignature1) ==> (appliedTerm1 === structuralTerm1)))
          // println(forallSeq(variables2, wellTypedFormula(semanticSignature2) ==> (appliedTerm2 === structuralTerm)))
          have(forallSeq(variables2, wellTypedFormula(semanticSignature2) ==> (appliedTerm2 === structuralTerm2))) by Restate.from(shortDefinition)

          variables2.foldLeft(lastStep)((fact, v) =>
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
                case _ => throw UnreachableException
            )
          val tappTerm2Def = thenHave(vars2WellTyped |- appliedTerm2 === structuralTerm2) by Restate


          val s0 = have(vars2WellTyped + (appliedTerm1 === appliedTerm2) |- appliedTerm1 === structuralTerm2) by Cut(tappTerm2Def,
            ADTThm.altEqualityTransitivity of (x := appliedTerm1, y := appliedTerm2, z := structuralTerm2))
          have(vars1WellTyped + (appliedTerm1 === structuralTerm2) |- structuralTerm1 === structuralTerm2) by Cut(tappTerm1Def,
            ADTThm.altEqualityTransitivity of (x := structuralTerm1, y := appliedTerm1, z := structuralTerm2))
          have((vars1WellTyped ++ vars2WellTyped) + (appliedTerm1 === appliedTerm2) |- structuralTerm1 === structuralTerm2) by Cut(s0, lastStep)
          val forward = thenHave(vars1WellTyped ++ vars2WellTyped |- (appliedTerm1 === appliedTerm2) ==> (structuralTerm1 === structuralTerm2)) by RightImplies

          val s1 = have(vars1WellTyped + (structuralTerm1 === structuralTerm2) |- appliedTerm1 === structuralTerm2) by Cut(tappTerm1Def,
            ADTThm.altEqualityTransitivity of (x := appliedTerm1, y := structuralTerm1, z := structuralTerm2))
          have(vars2WellTyped + (appliedTerm1 === structuralTerm2) |- appliedTerm1 === appliedTerm2) by Cut(tappTerm2Def,
            ADTThm.altEqualityTransitivity of (x := appliedTerm1, y := structuralTerm2, z := appliedTerm2))
          have((vars1WellTyped ++ vars2WellTyped) + (structuralTerm1 === structuralTerm2) |- appliedTerm1 === appliedTerm2) by Cut(s1, lastStep)
          val backward = thenHave(vars1WellTyped ++ vars2WellTyped |- (structuralTerm1 === structuralTerm2) ==> (appliedTerm1 === appliedTerm2)) by RightImplies

          val definitionUnfolding = have(vars1WellTyped ++ vars2WellTyped |- (appliedTerm1 === appliedTerm2) <=> (structuralTerm1 === structuralTerm2)) by RightIff(forward, backward)
          have((appliedTerm1 === appliedTerm2) <=> (structuralTerm1 === structuralTerm2) |- (appliedTerm1 === appliedTerm2) <=> /\(variables1.zip(variables2).map(_ === _))) by Sorry
          Cut(
            underlying.injectivity,
            ADTThm.equivalenceRewriting of (p1 := (appliedTerm1 === appliedTerm2), p2 := (structuralTerm1 === structuralTerm2), p3 := /\(variables1.zip(variables2).map(_ === _)))
          )
          have(thesis) by Cut(definitionUnfolding, lastStep)
        }

    
    /**
     * Case generated by this constructor when performing a proof by induction
     */
    lazy val inductiveCase: Formula =
      syntacticSignature.foldRight[Formula](P(appliedTerm1))
        ((el, fc) =>
          val (v, typ) = el
          typ match
            case Self => forall(v, v :: adt.term ==> (P(v) ==> fc))
            case GroundType(t) => forall(v, v :: t ==> fc)
        )  
}

/**
  * Semantic set theoretical interpretation of an algebraic data type. That is the least set closed under [[SemanticConstructor]].
  * 
  * E.g. list is the smallest set containing nil and closed under the cons function.
  *  
  * Injectivity between different constructors, structural induction and elimination rule are proved within this class.
  *
  * @constructor generates a semantic interpretation for this ADT out of a syntactic one
  * @param underlying the syntactic representation of this ADT
  * @param constructors constructors of this ADT
  */
  private class SemanticADT[N <: Arity](
    val underlying: SyntacticADT[N], 
    val constructors: Seq[SemanticConstructor[N]]
    ) {

    /**
     * Name of this ADT.
     */
    val name: String = underlying.name

    /**
      * Identifier of this ADT.
      */
    val id: Identifier = underlying.polymorphicTerm.id

    /**
     * Type variables of this ADT.
     */
    val typeVariables: Variable ** N = underlying.typeVariables

    /**
      * Sequence of type variables of this ADT.
      */
    val typeVariablesSeq: Seq[Variable] = underlying.typeVariablesSeq

    /**
      * Number of type variables in this ADT.
      */
    val typeArity: N = underlying.typeArity

    /**
     * Term representing this ADT where type variables are instantiated with given arguments.
     * 
     * @param args the instances of this ADT type variables
     */
    def term(args: Seq[Term]) = underlying.polymorphicTerm.applySeq(args)

    /**
     * Term representing this ADT where type variables are instantiated with schematic variables.
     */
    val term: Term = underlying.term

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of different construcors are always different.
     *
     * e.g. Nil != Cons(head, tail)
     */
    def injectivity(c1: SemanticConstructor[N], c2: SemanticConstructor[N]) =

      val vars1WellTyped: Set[Formula] = wellTypedSet(c1.semanticSignature1)
      val vars2WellTyped: Set[Formula] = wellTypedSet(c2.semanticSignature2)

      Lemma(vars1WellTyped ++ vars2WellTyped |- !(c1.appliedTerm1 === c2.appliedTerm2)) {

        val defUnfolding = have((vars1WellTyped ++ vars2WellTyped) + (c1.appliedTerm1 === c2.appliedTerm2) |- c1.structuralTerm1 === c2.structuralTerm2) subproof {
          have(forallSeq(c1.variables1, wellTypedFormula(c1.semanticSignature1) ==> (c1.appliedTerm1 === c1.structuralTerm1))) by Restate.from(c1.shortDefinition)

          c1.variables1.foldLeft(lastStep)((fact, v) =>
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi.substitute(v := x)) by InstantiateForall(x)
              case _ => throw UnreachableException
          )
          val tappTerm1Def = thenHave(vars1WellTyped |- c1.structuralTerm1 === c1.appliedTerm1) by Restate

          have(forallSeq(c2.variables2, wellTypedFormula(c2.semanticSignature2) ==> (c2.appliedTerm2 === c2.structuralTerm2))) by Restate.from(c2.shortDefinition)

          c2.variables2.foldLeft(lastStep)((fact, v) =>
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException
          )
          val tappTerm2Def = thenHave(vars2WellTyped |- c2.appliedTerm2 === c2.structuralTerm2) by Restate

          val s0 = have(vars2WellTyped + (c1.appliedTerm1 === c2.appliedTerm2) |- c1.appliedTerm1 === c2.structuralTerm2) by Cut(
            tappTerm2Def,
            ADTThm.altEqualityTransitivity of (x := c1.appliedTerm1, y := c2.appliedTerm2, z := c2.structuralTerm2)
          )
          have(vars1WellTyped + (c1.appliedTerm1 === c2.structuralTerm2) |- c1.structuralTerm1 === c2.structuralTerm2) by Cut(
            tappTerm1Def,
            ADTThm.altEqualityTransitivity of (x := c1.structuralTerm1, y := c1.appliedTerm1, z := c2.structuralTerm2)
          )
          have(thesis) by Cut(s0, lastStep)
        }

        have(!(c1.structuralTerm1 === c2.structuralTerm2)) by Restate.from(underlying.injectivity(c1.underlying, c2.underlying))
        thenHave(c1.structuralTerm1 === c2.structuralTerm2 |- ()) by Restate

        have((vars1WellTyped ++ vars2WellTyped) + (c1.appliedTerm1 === c2.appliedTerm2) |- ()) by Cut(defUnfolding, lastStep)
      }

    /**
     * Theorem --- Structural induction principle for this ADT.
     *
     *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
     */
    lazy val induction = Lemma(constructors.foldRight[Formula](forall(x, x :: term ==> P(x)))((c, f) => c.inductiveCase ==> f)) { sp ?=>
      constructors.foldRight[(Formula, Formula, sp.Fact)] {
        val prop = forall(x, x :: term ==> P(x))
        (prop, prop, have(prop <=> prop) by Restate)
      }((c, acc) =>
        val (oldBefore, oldAfter, fact) = acc
        val newBefore = underlying.inductiveCase(c.underlying) ==> oldBefore
        val newAfter = c.inductiveCase ==> oldAfter

        have(underlying.inductiveCase(c.underlying) <=> c.inductiveCase) subproof {
          val wellTypedVars: Seq[Formula] = wellTyped(c.semanticSignature)
          val wellTypedVarsSet = wellTypedVars.toSet


          have(forallSeq(c.variables, wellTypedFormula(c.semanticSignature) ==> (c.appliedTerm === c.structuralTerm))) by Restate.from(c.shortDefinition)
          if c.arity > 0 then
            c.variables1.foldLeft(lastStep)((l, _) =>
              lastStep.statement.right.head match
                case Forall(v, phi) => thenHave(phi) by InstantiateForall(v)
                case _ => throw UnreachableException
            )

          val eq = thenHave(wellTypedVarsSet |- c.appliedTerm === c.structuralTerm) by Restate
          have(P(c.appliedTerm) <=> P(c.appliedTerm)) by Restate
          thenHave(c.structuralTerm === c.appliedTerm |- P(c.structuralTerm) <=> P(c.appliedTerm)) by RightSubstEq.withParametersSimple(
            List((c.structuralTerm, c.appliedTerm)),
            lambda(s, P(c.structuralTerm) <=> P(s))
          )
          have(wellTypedVarsSet |- P(c.structuralTerm) <=> P(c.appliedTerm)) by Cut(eq, lastStep)

          c.syntacticSignature
            .foldRight[(Formula, Formula, Seq[Formula])]((P(c.structuralTerm), P(c.appliedTerm), wellTypedVars))((el, fc) =>
              val (v, ty) = el
              val (fc1, fc2, wellTypedVars) = fc
              ty match
                case Self =>
                  val wellTypedV: Formula = v :: term
                  have(wellTypedVars |- (P(v) ==> fc1) <=> (P(v) ==> fc2)) by Cut(lastStep, ADTThm.leftImpliesEquivalenceWeak of (p := P(v), p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- wellTypedV ==> ((P(v) ==> fc1) <=> (P(v) ==> fc2))) by RightImplies
                  have(wellTypedVars.init |- (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2))) by Cut(
                    lastStep,
                    ADTThm.leftImpliesEquivalenceStrong of (p := wellTypedV, p1 := P(v) ==> fc1, p2 := P(v) ==> fc2)
                  )
                  thenHave(wellTypedVars.init |- forall(v, (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2)))) by RightForall
                  have(wellTypedVars.init |- forall(v, (wellTypedV ==> (P(v) ==> fc1))) <=> forall(v, (wellTypedV ==> (P(v) ==> fc2)))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, wellTypedV ==> (P(v) ==> fc1)), Q := lambda(v, wellTypedV ==> (P(v) ==> fc2)))
                  )
                  (forall(v, wellTypedV ==> (P(v) ==> fc1)), forall(v, wellTypedV ==> (P(v) ==> fc2)), wellTypedVars.init)
                case GroundType(t) =>
                  thenHave(wellTypedVars.init |- v :: t ==> (fc1 <=> fc2)) by RightImplies
                  have(wellTypedVars.init |- (in(v, t) ==> fc1) <=> (v :: t ==> fc2)) by Cut(lastStep, ADTThm.leftImpliesEquivalenceStrong of (p := in(v, t), p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- forall(v, (in(v, t) ==> fc1) <=> (v :: t ==> fc2))) by RightForall
                  have(wellTypedVars.init |- forall(v, (in(v, t) ==> fc1)) <=> forall(v, (v :: t ==> fc2))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, in(v, t) ==> fc1), Q := lambda(v, v :: t ==> fc2))
                  )
                  (forall(v, (in(v, t) ==> fc1)), forall(v, (v :: t ==> fc2)), wellTypedVars.init)
            )
        }
        (newBefore, newAfter, have(newBefore <=> newAfter) by Apply(ADTThm.impliesEquivalence).on(lastStep, fact))
      )
      have(underlying.induction.statement.right.head |- thesis.right.head) by Cut(
        lastStep,
        ADTThm.equivalenceApply of (
          p1 := underlying.induction.statement.right.head, p2 := thesis.right.head
        )
      )
      have(thesis) by Cut(underlying.induction, lastStep)
    }

    /**
      * Returns a map binding each constructor to formula describing whether x is an instance of it.
      */
    private lazy val isConstructorMap: Map[SemanticConstructor[N], Formula] =
      constructors.map(c => c -> existsSeq(c.variables, wellTypedFormula(c.semanticSignature) /\ (x === c.appliedTerm))).toMap

    /**
      * Returns a formula describing whether x is an instance of one of this ADT's constructors.
      */
    private lazy val isConstructor =
      \/(constructors.map(c => isConstructorMap(c)))

    /**
     * Theorem --- Pattern matching principle (also known as elimination rule) for this ADT.
     *
     *    `x ∈ ADT |- x = c * x1 * ... * xn for some constructor c and xi, ..., xj ∈ ADT`
     */
    lazy val elim = Lemma(x :: term |- simplify(isConstructor)) {

      // Induction preconditions with P(z) = z != x
      val inductionPreconditionIneq = constructors.map(c => c -> c.inductiveCase.substitute((P -> lambda(z, !(x === z))))).toMap
      val inductionPreconditionsIneq = /\(inductionPreconditionIneq.map(_._2))

      // Weakening of the negation of the induction preconditions
      val weakNegInductionPreconditionIneq: Map[SemanticConstructor[N], Formula] = constructors
        .map(c =>
          c ->
            c.semanticSignature
              .foldRight[Formula](x === c.appliedTerm)((el, fc) =>
                val (v, t) = el
                exists(v, (v :: t) /\ fc)
              )
        )
        .toMap

      // STEP 1: Prove that if the induction preconditions with P(z) = z != x do not hold then x is the instance of some constructor
      val strengtheningOfInductionPreconditions = have(!inductionPreconditionsIneq |- isConstructor) subproof {
        if constructors.isEmpty then have(thesis) by Restate
        else

          // STEP 1.1: Prove the claim for each constructor
          val negInductionPreconditionsOrSequence =
            for c <- constructors yield

              // STEP 1.1.1: Prove the strengthening of the negations of the induction preconditions
              val conditionStrenghtening = have(!inductionPreconditionIneq(c) |- weakNegInductionPreconditionIneq(c)) subproof {
                have(x === c.appliedTerm |- x === c.appliedTerm) by Hypothesis

                c.syntacticSignature
                  .foldRight(lastStep)((el, fact) =>
                    val (v, ty) = el
                    val left = fact.statement.left.head
                    val right = fact.statement.right.head

                    ty match
                      case Self =>
                        thenHave(!(x === v) /\ left |- right) by Weakening
                      case _ => ()

                    val weakr = thenHave(in(v, ty.getOrElse(term)) /\ left |- right) by Weakening
                    val weakl = have(in(v, ty.getOrElse(term)) /\ left |- in(v, ty.getOrElse(term))) by Restate

                    have((v :: ty.getOrElse(term)) /\ left |- (v :: ty.getOrElse(term)) /\ right) by RightAnd(weakl, weakr)
                    thenHave((v :: ty.getOrElse(term)) /\ left |- exists(v, (v :: ty.getOrElse(term)) /\ right)) by RightExists
                    thenHave(exists(v, (v :: ty.getOrElse(term)) /\ left) |- exists(v, (v :: ty.getOrElse(term)) /\ right)) by LeftExists
                  )

              }

              // STEP 1.1.2: Conclude
              // TODO: Change to a more efficient way of proving this
              have(weakNegInductionPreconditionIneq(c) |- isConstructorMap(c)) by Tableau
              have(!inductionPreconditionIneq(c) |- isConstructorMap(c)) by Cut(conditionStrenghtening, lastStep)
              thenHave(!inductionPreconditionIneq(c) |- isConstructor) by Weakening

          have(thesis) by LeftOr(negInductionPreconditionsOrSequence*)
      }

      // STEP 2: Conclude
      have(inductionPreconditionsIneq |- forall(z, z :: term ==> !(x === z))) by Restate.from(induction of (P := lambda(z, !(x === z))))
      thenHave(inductionPreconditionsIneq |- x :: term ==> !(x === x)) by InstantiateForall(x)
      val ind = thenHave(x :: term |- !inductionPreconditionsIneq) by Restate
      have(x :: term |- isConstructor) by Cut(lastStep, strengtheningOfInductionPreconditions)
    }
  }
