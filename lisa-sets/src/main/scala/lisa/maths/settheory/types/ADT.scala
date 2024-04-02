package lisa.maths.settheory.types

import lisa.SetTheoryLibrary
import lisa.maths.settheory.SetTheory.*
import lisa.maths.Quantifiers.*

import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.OutputManager
import lisa.prooflib.Library

import scala.collection.immutable.HashMap
import lisa.utils.parsing.UnreachableException
import lisa.maths.settheory.types.TypeLib.{any, |=>, given}
import lisa.maths.settheory.types.TypeSystem.{*, given}
import lisa.prooflib.SimpleDeducedSteps.InstantiateForall

object ADTHelperDefinitions {

  def benchmark[T](name: String)(f: => T): T = {
    val before = System.nanoTime

    val res = f

    val totalTime = (System.nanoTime - before) / 1000000

    println(s"$name time: $totalTime ms")

    res
  }

  // *********************
  // * FIRST ORDER LOGIC *
  // *********************

  /**
   * Formula representing whether two sequences of terms are pairwise equal.
   *
   * @param s2 the sequence to compare with
   */
  extension (s1: Seq[Term]) def ===(s2: Seq[Term]): Formula = /\(s1.zip(s2).map(_ === _))

  /**
   * Disjunction of a sequence of formulas.
   *
   * @param s the formulas to which the disjunction is applied
   */
  def \/(s: Iterable[Formula]): Formula =
    if s.isEmpty then False
    else s.fold(False)(_ \/ _)

  /**
   * Conjunction of a sequence of formulas.
   *
   * @param s the formulas to which the conjunction is applied
   */
  def /\(s: Iterable[Formula]): Formula =
    if s.isEmpty then True
    else s.fold(True)(_ /\ _)

  /**
   * Repeats existential quantification over a sequence of variables.
   *
   * @param vars the variables to quantify over
   * @param f the formula to which the quantifiers are applied
   * @return the quantified formula
   */
  def existsSeq(vars: Seq[Variable], f: Formula): Formula =
    vars.foldRight(f)(exists(_, _))

  /**
   * Repeats universal quantification over a sequence of variables.
   *
   * @param vars the variables to quantify over
   * @param f the formula to which the quantifiers are applied
   * @return the quantified formula
   */
  def forallSeq(vars: Seq[Variable], f: Formula): Formula =
    vars.foldRight(f)(forall(_, _))

  /**
   * Simplifies a formula by removing True and False constants.
   *
   * @param f the formula to simplify
   */
  def simplify(f: Formula): Formula =
    f match
      case Or(False, phi) => simplify(phi)
      case Or(phi, False) => simplify(phi)
      case Or(phi, psi) => simplify(phi) \/ simplify(psi)
      case And(True, phi) => simplify(phi)
      case And(phi, True) => simplify(phi)
      case And(phi, psi) => simplify(phi) /\ simplify(psi)
      case Implies(True, phi) => simplify(phi)
      case Implies(phi, psi) => Implies(simplify(phi), simplify(psi))
      case _ => f

  // ********
  // * ADTS *
  // ********

  /**
   * The signature of a constructor can either contain terms or a self reference, i.e. a reference to the ADT itself.
   */
  type ConstructorArgument = Self.type | Term

  /**
   * Self reference to the ADT.
   */
  object Self

  /**
   * Returns the term associated to a constructor argument, or in case it is a self reference, returns the term associated to the ADT.
   *
   * @param t the constructor argument
   * @param adt the term representing the ADT
   */
  def getOrElse(t: ConstructorArgument, adt: Term): Term =
    t match {
      case Self => adt
      case term: Term => term
    }

  /**
   * Shorthand for the union of the range of a function.
   *
   * @param f the function
   */
  def unionRange(f: Term) = union(relationRange(f))

  /**
   * Shorthand for the range of a restricted function.
   *
   * @param f the function
   * @param n the domain to which the function is restricted
   */
  def restrRange(f: Term, n: Term) = relationRange(restrictedFunction(f, n))

  /**
   * Applies a sequence of arguments to a function.
   *
   * @param f the function
   * @param args the arguments to apply
   */
  def appSeq(f: Term)(args: Seq[Term]): Term = args.foldLeft(f)(_ * _)

  /**
   * Converts an integer to the associated ordinal.
   *
   * @param n the integer to convert
   */
  def toTerm(n: Int): Term =
    require(n >= 0, "n must be a non-negative integer")
    if n == 0 then emptySet
    else successor(toTerm(n - 1))

}



/**
 * This object implements tactic to generate algebraic data types (or ADT) and prove properties about them.
 * An algebraic data type is the least set closed under introduction rules, also known as constructors.
 * A constructor takes arguments as input that can either belong to other types (non inductive arguments)
 * or to the ADT itself (inductive arguments).
 *
 * An example of algebraic data type is the type of boolean lists. Lists can be either empty or can result from
 * the addition of an element to a preexisting list. Formally we define them with the following constructors
 *
 *   boollist ::= nil() | cons(head: B, tail: boollist)
 */
object ADTTactic {

  import ADTHelperTheorems.*
  import ADTHelperDefinitions.*
  import ADTHelperDefinitions.{/\, \/, ===}

  /**
   * Variable imports
   */
  val schemPred = predicate[1]

  /**
   * Helpers for constructors
   */
  object Constructors {

    /**
     * Global counter used to uniquely identify constructors and thereby avoid structural subtyping.
     */
    var tagCounter = 0
  }

  /**
   * Constructor of an algebraic data type.
   *
   * @param name name of the constructor
   * @param signature types of the arguments of the constructor
   */
  class UntypedConstructor(using line: sourcecode.Line, file: sourcecode.File)(val name: String, val signature: Seq[ConstructorArgument]) {

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
     * Number of arguments that this constructor takes
     */
    val arity: Int = signature.length

    /**
     * List of type variables appearing in the signature of this constructor
     */
    val typeVariables: Seq[Variable] =

      /**
       * Extracts the type variables from a term
       */
      def typeVariables(t: Term): Seq[Variable] =
        t match
          case v: Variable => Seq(v)
          case _: Constant => Seq.empty
          case af: AppliedFunctional => af.args.flatMap(typeVariables)

      signature
        .flatMap({
          case Self => Seq.empty
          case te: Term => typeVariables(te)
        })
        .distinct

    /**
     * List of variables used in the definition of this constructor
     */
    val variables: Seq[Variable] = for i <- 0 until arity yield Variable(s"a${i}")

    /**
     * Alternative set of variables to used to avoid capture issues.
     * This is particularly useful when working with quantifiers.
     */
    val quantifiedVariables: Seq[Variable] = for i <- 0 until arity yield Variable(s"b${i}")

    /**
     * Internally, an instance of this constructor is represented as a list.
     * The first element of this list is the tag of this constructor.
     * The following elements are its arguments. We represent lists as chained
     * pairs followed by the empty set.
     *
     * e.g. cons(1, nil()) --> (tagcons, (1, ((tagnil, ∅), ∅)))
     *
     * @param targs the type arguments of this instance of the constructor
     * @param args the arguments of this instance of the constructor
     */
    def term(targs: Seq[Term], args: Seq[Term]): Term = pair(tagTerm, subterm(targs, args))

    def term(args: Seq[Term]): Term = term(typeVariables, args)

    val term: Term = term(variables)

    val termWithQuantifiedVars: Term = term(quantifiedVariables)

    /**
     * Internal representation of an instance of this constructor without the tag
     *
     * @param targs the type arguments of this instance of the constructor
     * @param args the arguments of this instance of the constructor
     *
     * @see [[this.term]]
     */
    def subterm(targs: Seq[Term], args: Seq[Term]): Term = args.foldRight(emptySet)((t, acc: Term) => pair(t.substitute(typeVariables.zip(targs).map(_ := _): _*), acc))

    def subterm(args: Seq[Term]): Term = subterm(typeVariables, args)

    val subterm: Term = subterm(variables)

    val subtermWithQuantifiedVars: Term = subterm(quantifiedVariables)

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
     *
     * e.g. cons(head1, tail1) === cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
     */
    lazy val injectivity =

      // STEP 1: Choose two different sets of variables. For convenience, we choose already existing set of variables.
      val vars1 = variables
      val vars2 = quantifiedVariables

      // STEP 2: Caching
      val term1 = term
      val term2 = termWithQuantifiedVars
      val subterm1 = subterm
      val subterm2 = subtermWithQuantifiedVars

      if arity == 0 then
        Lemma(term1 === term2) {
          have(thesis) by RightRefl
        }
      else
        Lemma((term1 === term2) <=> /\(vars1.zip(vars2).map(_ === _))) {

          // STEP 3: Get rid of the tag using pair extensionality
          have((term1 === term2) <=> (subterm1 === subterm2)) by Restate.from(pairExtensionality of (a := tagTerm, b := subterm1, c := tagTerm, d := subterm2))

          // STEP 4: Repeat pair extensionality until all variables have been pulled out of the term
          vars1
            .zip(vars2)
            .foldLeft(Seq.empty[Variable], vars1, Seq.empty[Variable], vars2, lastStep)((acc, v) =>

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
                rightAndEquivalence of (p := pulledVars1 === pulledVars2, p1 := pair(v1, subsubterm1) === pair(v2, subsubterm2), p2 := (v1 === v2) /\ (subsubterm1 === subsubterm2))
              )
              val newFact = have(
                (term1 === term2) <=>
                  ((updatedPulledVars1 === updatedPulledVars2) /\ (subsubterm1 === subsubterm2))
              ) by Apply(equivalenceRewriting).on(lastStep, previousFact)

              (updatedPulledVars1, updatedRemainingVars1, updatedPulledVars2, updatedRemainingVars2, newFact)
            )
        }

  }

  class UntypedADT(using line: sourcecode.Line, file: sourcecode.File)(val name: String, val constructors: Seq[UntypedConstructor]) {

    // *************************
    // * INTRODUCTION FUNCTION *
    // *************************

    /**
     * Formula describing whether the arguments of a constructor belongs to their respective domain or s when they are self-referencing.
     *
     * @param c The considered constructor
     * @param args The arguments of the constructor
     * @param s The set of elements in which self-referencing arguments of the constructor are.
     */
    private def constructorArgsInDomain(c: UntypedConstructor, args: Seq[Term], s: Term): Formula =
      /\(args.zip(c.signature).map((v, t) => in(v, getOrElse(t, s))))

    /**
     * Formula describing whether the variables of a constructor belongs to their respective domain or s when they are self-referencing.
     *
     * @param c The considered constructor
     * @param s The set of elements in which self-referencing variables of the constructor are.
     */
    private def constructorVarsInDomain(c: UntypedConstructor, s: Term): Formula = constructorArgsInDomain(c, c.variables, s)

    /**
     * Formula describing whether the quantified variables of a constructor belongs to their respective domain or s when they are self-referencing.
     * The quantified variables of a constructor are an alternative set of variables then the ones used in its definition. They are
     * used to avoid capture issues when dealing with quantifiers.
     *
     * @see [[UntypedConstructor.quantifiedVariables]].
     *
     * @param c The considered constructor
     * @param s The set of elements in which self-referencing variables of the constructor are.
     */
    private def constructorQuantifiedVarsInDomain(c: UntypedConstructor, s: Term): Formula = constructorArgsInDomain(c, c.quantifiedVariables, s)

    /**
     * Formula describing whether an element x is an instance of a specific constructor.
     *
     * @param c The constructor we want to check if x is an instance of
     * @param x The element we want to check if it is an instance of c
     * @param s The set of elements in which self-referencing arguments of the constructor are.
     */
    private def isConstructor(c: UntypedConstructor, x: Term, s: Term): Formula =
      existsSeq(c.quantifiedVariables, constructorQuantifiedVarsInDomain(c, s) /\ (x === c.termWithQuantifiedVars))

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
     *    introductionFunction(s) = {y | y = c(a1, ..., an) for some c ∈ constructors and a1, ..., an ∈ s} ∪ s
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
      have(subsetST |- forall(z, in(z, s) ==> in(z, t))) by Apply(equivalenceApply of (p1 := subsetST)).on(subsetAxiom.asInstanceOf)
      val subsetElimination = thenHave(subsetST |- in(z, s) ==> in(z, t)) by InstantiateForall(z)

      // STEP 2: For each constructor, prove that if x is an instance of that constructor with self referencing arguments in s
      // then it is also an instance of some constructor with self referencing arguments in t
      val isConstructorXSImpliesT =
        for c <- constructors yield
          // STEP 2.0: Caching predicates that are often used
          // TODO change identifier
          val labelEq = c.termWithQuantifiedVars === x
          val isConstructorCXS = isConstructor(c, x, s)
          val isConstructorCXT = isConstructor(c, x, t)
          val consQuantVarsInDomainS = constructorQuantifiedVarsInDomain(c, s)
          val consQuantVarsInDomainT = constructorQuantifiedVarsInDomain(c, t)

          if c.arity == 0 then have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
          else
            // STEP 2.1: Prove that we can expand the domain of the (quantified) variables of the constructor
            val andSeq =
              for ((v, ty) <- c.quantifiedVariables.zip(c.signature)) yield have((subsetST, consQuantVarsInDomainS) |- in(v, getOrElse(ty, t))) by Weakening(subsetElimination of (z := v))
            val expandingDomain = have((subsetST, consQuantVarsInDomainS) |- consQuantVarsInDomainT) by RightAnd(andSeq: _*)
            val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
            have((subsetST, consQuantVarsInDomainS, labelEq) |- consQuantVarsInDomainT /\ labelEq) by RightAnd(expandingDomain, weakeningLabelEq)

            // STEP 2.2: Prove that x stays an instance of this constructor if we expand the domain of the variables
            thenHave((subsetST, consQuantVarsInDomainS, labelEq) |- isConstructorCXT) by QuantifiersIntro(c.quantifiedVariables)
            thenHave((subsetST, consQuantVarsInDomainS /\ labelEq) |- isConstructorCXT) by LeftAnd
            thenHave((subsetST, isConstructorCXS) |- isConstructorCXT) by QuantifiersIntro(c.quantifiedVariables)

            // STEP 2.3: Weaken the conclusion to some constructor instead of a specific one
            thenHave((subsetST, isConstructorCXS) |- isConstructorXT) by Weakening

      // STEP 3: Prove that this holds for any constructor
      // ? Steps 2 and 3 can be merged and optimized through the repeated use of an external theorem like [[ADTHelperTheorems. unionPreimageMonotonic]]
      if constructors.isEmpty then have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
      else have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(isConstructorXSImpliesT: _*)

      // STEP 4: Prove the thesis by showing that making the union with the function argument does not change the monotonicity
      thenHave(subsetST |- isConstructorXS ==> isConstructorXT) by RightImplies
      have(thesis) by Cut(lastStep, unionPreimageMonotonic of (P := lambda(s, isConstructorXS)))
    }

    /**
     * Lemma --- Every constructor is in the image of the introduction function.
     *
     *      `For every c ∈ constructors, ai ∈ s, ..., aj ∈ s |- c(a1, ..., an) ∈ introductionFunction(s)`
     */
    private val constructorIsInIntroductionFunction = constructors
      .map(c =>
        c -> Lemma(constructorVarsInDomain(c, s) |- isInIntroductionFunctionImage(s)(c.term)) {

          // Caching
          val constructorVarsInDomainCS = constructorVarsInDomain(c, s)

          have(constructorVarsInDomainCS |- constructorVarsInDomainCS /\ (c.term === c.term)) by Restate

          // Replace each variable on the LHS of the equality by a quantified variable and then introduce an existential quantifier
          (c.quantifiedVariables).foldRight((c.variables, List[Variable]()))((v, acc) =>

            // At each step remove a variable and add a quantified one
            val oldVariables = acc._1.init
            val newVariables = v :: acc._2
            val vars = oldVariables ++ newVariables

            thenHave(constructorVarsInDomainCS |- existsSeq(newVariables, constructorArgsInDomain(c, vars, s) /\ (c.term(vars) === c.term))) by RightExists

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
        unionRangeMonotonic,
        introductionFunctionMononotic of (s := unionRange(f), t := unionRange(g))
      )
      val left = thenHave((subset(f, g), introFunUnionRangeF) |- introFunUnionRangeG) by Restate

      // STEP 2: Conclude by applying the conjuction on both sides
      have((subset(f, g), !(f === emptySet), introFunUnionRangeF) |- isInExtendedIntroductionFunctionImage(g)(x)) by RightAnd(left, subsetNotEmpty of (x := f, y := g))
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
      have(thesis) by Apply(existsOneImpliesExists of (P := lambda(h, hIsTheHeightFunction))).on(heightFunUniqueness.asInstanceOf)
    }

    /**
     * Lemma --- If two functions are the height function then they are the same.
     *
     *     `f = height /\ h = height => f = h`
     */
    private val heightFunctionUniqueness2 = Lemma((fIsTheHeightFunction, hIsTheHeightFunction) |- f === h) {
      have(thesis) by Cut(heightFunUniqueness, existsOneUniqueness of (P := lambda(h, hIsTheHeightFunction), x := f, y := h))
    }

    /**
     * Lemma --- The height function is not empty.
     *
     *     `height ≠ ∅`
     */
    private val heightFunctionNonEmpty = Lemma(hIsTheHeightFunction |- !(h === emptySet)) {
      // The proof goes by contradiction. If the height function is empty then its domain is empty as well.
      // This would imply that the set of natural numbers is empty, which is a contradiction.
      have(N === emptySet |- ()) by Restate.from(natNotEmpty)
      thenHave((relationDomain(h) === emptySet, relationDomain(h) === N, relationDomain(h) === relationDomain(h)) |- ()) by LeftSubstEq.withParametersSimple(
        List((relationDomain(h), emptySet), (relationDomain(h), N)),
        lambda((x, y), y === x)
      )
      thenHave((relationDomain(h) === N, relationDomain(h) === relationDomain(h)) |- !(relationDomain(h) === emptySet)) by RightNot
      have(thesis) by Apply(nonEmptyDomain).on(lastStep)
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
      have((hIsTheHeightFunction, in(n, N), subset(m, n)) |- in(x, app(h, m)) <=> extendedIntroFunRestrictedFunM) by Apply(heightApplication).on(subsetIsNat.asInstanceOf)
      val unfoldHeightApplicationM = have((hIsTheHeightFunction, in(n, N), subset(m, n), in(x, app(h, m))) |- extendedIntroFunRestrictedFunM) by Cut(
        lastStep,
        equivalenceRevApply of (p1 := in(x, app(h, m)), p2 := extendedIntroFunRestrictedFunM)
      )

      // STEP 2: Use the monotonicity of the extended introduction function
      have(subset(m, n) |- extendedIntroFunRestrictedFunM ==> isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)) by Cut(
        restrictedFunctionDomainMonotonic of (x := m, y := n, f := h),
        extendedIntroductionFunctionMonotonic of (f := restrictedFunction(h, m), g := restrictedFunction(h, n))
      )
      have((hIsTheHeightFunction, in(n, N), subset(m, n), extendedIntroFunRestrictedFunM) |- in(x, app(h, n))) by Apply(equivalenceRevApply).on(lastStep, heightApplication.asInstanceOf)

      // STEP 3: Fold the definition of subset
      have((hIsTheHeightFunction, in(n, N), subset(m, n), in(x, app(h, m))) |- in(x, app(h, n))) by Cut(unfoldHeightApplicationM, lastStep)
      thenHave((hIsTheHeightFunction, in(n, N), subset(m, n)) |- in(x, app(h, m)) ==> in(x, app(h, n))) by RightImplies
      thenHave((hIsTheHeightFunction, in(n, N), subset(m, n)) |- forall(x, in(x, app(h, m)) ==> in(x, app(h, n)))) by RightForall
      have(thesis) by Apply(equivalenceRevApply).on(lastStep, subsetAxiom.asInstanceOf)
    }

    /**
     * Lemma --- There is no element of height 0 in the ADT.
     *
     *     `!∃x ∈ adt. height(x) = 0`
     */
    private val heightZero = Lemma(hIsTheHeightFunction |- !in(x, app(h, emptySet))) {

      // This is due to the fact that the extended introduction function is the empty set when the function is empty
      // (which happens when the height is set to 0).
      have(hIsTheHeightFunction |- in(x, app(h, emptySet)) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, emptySet))(x)) by Cut(zeroIsNat, heightApplication of (n := emptySet))
      thenHave((restrictedFunction(h, emptySet) === emptySet, hIsTheHeightFunction) |- !in(x, app(h, emptySet))) by
        RightSubstEq.withParametersSimple(
          List((restrictedFunction(h, emptySet), emptySet)),
          lambda(s, in(x, app(h, emptySet)) <=> isInExtendedIntroductionFunctionImage(s)(x))
        )
      have(thesis) by Cut(restrictedFunctionEmptyDomain, lastStep)
    }

    /**
     * Lemma --- The set of elements of height n + 1 is the set of elements of height n to which the introduction function is applied.
     *
     *     `height(n + 1) = introductionFunction(height(n))`
     */
    private val heightSuccessorWeak = Lemma((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) {

      // STEP 1: Prove that the restriction of height to n + 1 is not empty
      val restrHeightNotEmpty: Formula = !(restrictedFunction(h, successor(n)) === emptySet)
      have(!(h === emptySet) |- restrHeightNotEmpty) by Cut(zeroIsNotSucc, restrictedFunctionNotEmpty of (d := successor(n)))
      val restrHeightNotEmptyLemma = have(hIsTheHeightFunction |- restrHeightNotEmpty) by Cut(heightFunctionNonEmpty, lastStep)

      // STEP 2: Use the fact that if the function is cumulative then ∪ range(height | n + 1) = height(n) to conclude the proof
      have((hIsTheHeightFunction, in(n, N)) |- subset(m, n) ==> subset(app(h, m), app(h, n))) by RightImplies(heightMonotonic)
      thenHave((hIsTheHeightFunction, in(n, N)) |- forall(m, subset(m, n) ==> subset(app(h, m), app(h, n)))) by RightForall
      val unionRangeRestr = have((hIsTheHeightFunction, in(n, N)) |- unionRange(restrictedFunction(h, successor(n))) === app(h, n)) by Apply(unionRangeCumulativeRestrictedFunction).on(lastStep)

      have((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isInExtendedIntroductionFunctionImage(restrictedFunction(h, successor(n)))(x)) by Apply(heightApplication).on(
        equivalenceApply of (p1 := in(n, N)),
        successorIsNat.asInstanceOf
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

      have((hIsTheHeightFunction, in(n, N), restrHeightNotEmpty) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by Apply(equivalenceAnd of (p2 := restrHeightNotEmpty))
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
     * ConstructorArgument variables used in the definition of this ADT
     */
    val typeVariables: Seq[Variable] = constructors.flatMap(_.typeVariables).distinct

    /**
     * Class function defining the ADT. Takes as parameters the type variables of the ADT and return the set of all its instances.
     */
    val polymorphicTerm = FunctionDefinition(name, line.value, file.value)(typeVariables, z, termDefinition(z), termExistence).label

    /**
     * The set of all instances of the ADT where the type variables are not instantiated (i.e. are kept variable).
     */
    val term = polymorphicTerm.applySeq(typeVariables)

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

    // // *************************
    // // * TYPING / INTRODUCTION *
    // // *************************

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
        equivalenceApply of (p1 := in(x, term), p2 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))))
      )
      val termDefinitionBackward = have(forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- in(x, term)) by Cut(
        termDefinition,
        equivalenceRevApply of (p2 := in(x, term), p1 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))))
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
      have(hIsTheHeightFunction |- in(x, term) <=> ∃(n, in(n, relationDomain(h)) /\ in(x, app(h, n)))) by Apply(equivalenceRewriting).on(unionRangeMembership.asInstanceOf, lastStep)

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

          if c.variables.isEmpty then have(thesis) by Weakening(existsNat)
          else

            // STEP 1: Backward implication

            val backward = have(hIsTheHeightFunction |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) ==> constructorVarsInDomain(c, term)) subproof {
              val andSeq = for ((v, ty) <- c.variables.zip(c.signature)) yield ty match
                case Self =>
                  val termHasHeightBackward = have((hIsTheHeightFunction, exists(n, in(n, N) /\ in(v, app(h, n)))) |- in(v, term)) by Cut(
                    termHasHeight of (x := v),
                    equivalenceRevApply of (p1 := ∃(n, in(n, N) /\ in(v, app(h, n))), p2 := in(v, term))
                  )

                  have((in(n, N) /\ in(v, app(h, n))) |- in(n, N) /\ in(v, app(h, n))) by Restate
                  thenHave((in(n, N) /\ in(v, app(h, n))) |- exists(n, in(n, N) /\ in(v, app(h, n)))) by RightExists
                  have((hIsTheHeightFunction, in(n, N) /\ in(v, app(h, n))) |- in(v, term)) by Cut(lastStep, termHasHeightBackward)
                  thenHave((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, term)) by Weakening
                case t: Term =>
                  have((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, t)) by Restate

              have((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by RightAnd(andSeq: _*)
              thenHave((hIsTheHeightFunction, exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- constructorVarsInDomain(c, term)) by LeftExists
            }

            // STEP 2: Forward implication

            val forward = have(hIsTheHeightFunction |- constructorVarsInDomain(c, term) ==> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) subproof {
              val nSeq: Seq[Variable] = (0 until c.variables.size).map(i => Variable(s"n$i"))
              val max = if c.arity == 0 then emptySet else nSeq.reduce[Term](setUnion(_, _))

              val maxInN = have(/\(nSeq.map(n => in(n, N))) |- in(max, N)) by Sorry

              val andSeq = for ((v, ty), ni) <- c.variables.zip(c.signature).zip(nSeq) yield
                val niInMax = have(subset(ni, max)) by Sorry

                ty match
                  case Self =>
                    have((hIsTheHeightFunction, in(max, N), subset(ni, max)) |- subset(app(h, ni), app(h, max))) by Restate.from(heightMonotonic of (m := ni, n := max))
                    have((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- subset(app(h, ni), app(h, max))) by Sorry // Apply(lastStep).on(Seq(maxInN, niInMax), excluding = nSeq)
                    have((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- forall(z, in(z, app(h, ni)) ==> in(z, app(h, max)))) by Apply(equivalenceApply)
                      .on(Seq(lastStep, subsetAxiom), excluding = nSeq)
                    thenHave((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N)))) |- in(v, app(h, ni)) ==> in(v, app(h, max))) by InstantiateForall(v)
                    thenHave((hIsTheHeightFunction, /\(nSeq.map(n => in(n, N))), in(v, app(h, ni))) |- in(v, app(h, max))) by Restate
                  case t: Term =>
                    have((/\(nSeq.map(n => in(n, N))), hIsTheHeightFunction, in(v, t)) |- in(v, t)) by Restate

                have((/\(nSeq.map(n => in(n, N))), hIsTheHeightFunction, in(v, getOrElse(ty, app(h, ni)))) |- in(max, N) /\ in(v, getOrElse(ty, app(h, max)))) by RightAnd(maxInN, lastStep)
                thenHave(nSeq.map(n => in(n, N) /\ in(v, getOrElse(ty, app(h, n)))).toSet + hIsTheHeightFunction |- in(max, N) /\ in(v, getOrElse(ty, app(h, max)))) by Weakening
                thenHave(nSeq.map(n => in(n, N) /\ in(v, getOrElse(ty, app(h, n)))).toSet + hIsTheHeightFunction |- ∃(n, in(n, N) /\ in(v, getOrElse(ty, app(h, n))))) by RightExists

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
            equivalenceRevApply of (p1 := constructorInIntroFunHeight, p2 := in(c.term, app(h, successor(n))))
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
    val typing = constructors
      .map(c => {
        c ->
          Lemma(simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))) {
            // STEP 0: Instantiate the forward direction of termsHaveHeight.
            val termsHaveHeightForward = have((hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by Cut(
              termsHaveHeight(c),
              equivalenceApply of (p1 := constructorVarsInDomain(c, term), p2 := exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))
            )

            // STEP 1: Prove that if an instance of a constructor has height n + 1 then it is in this ADT.
            val left = have(in(n, N) |- in(successor(n), N)) by Cut(successorIsNat, equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N)))
            val right = have(in(c.term, app(h, successor(n))) |- in(c.term, app(h, successor(n)))) by Hypothesis
            have((in(n, N), in(c.term, app(h, successor(n)))) |- in(successor(n), N) /\ in(c.term, app(h, successor(n)))) by RightAnd(left, right)
            thenHave((in(n, N), in(c.term, app(h, successor(n)))) |- exists(m, in(m, N) /\ in(c.term, app(h, m)))) by RightExists
            have((hIsTheHeightFunction, in(n, N), in(c.term, app(h, successor(n)))) |- in(c.term, term)) by Apply(equivalenceRevApply).on(lastStep, termHasHeight.asInstanceOf)

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
          natInduction of (P := lambda(n, inductionFormulaN))
        )

        // STEP 1.2: Unfolding the definition of subset
        have(subset(app(h, n), app(h, successor(n))) |- forall(z, in(z, app(h, n)) ==> in(z, app(h, successor(n))))) by Cut(
          subsetAxiom of (x := app(h, n), y := app(h, successor(n))),
          equivalenceApply of (p1 := subset(app(h, n), app(h, successor(n))), p2 := forall(z, in(z, app(h, n)) ==> in(z, app(h, successor(n)))))
        )
        val subsetElimination = thenHave(subset(app(h, n), app(h, successor(n))) |- in(y, app(h, n)) ==> in(y, app(h, successor(n)))) by InstantiateForall(y)

        // STEP 1.3 : Use monotonicity to prove that y ∈ height(n) => y ∈ height(n + 1)
        have(in(n, N) |- in(successor(n), N)) by Cut(successorIsNat, equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N)))
        have((hIsTheHeightFunction, in(n, N), subset(n, successor(n))) |- subset(app(h, n), app(h, successor(n)))) by Cut(lastStep, heightMonotonic of (n := successor(n), m := n))
        have((hIsTheHeightFunction, in(n, N)) |- subset(app(h, n), app(h, successor(n)))) by Cut(subsetSuccessor, lastStep)
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
                val termWithQuantifiedVars = c.termWithQuantifiedVars
                val constructorQuantVarsInHN = constructorQuantifiedVarsInDomain(c, app(h, n))
                val constructorQuantVarsInHSuccN = constructorQuantifiedVarsInDomain(c, app(h, successor(n)))

                if c.arity == 0 then have((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorCXHSuccN) by Restate
                else
                  val liftHeightAndSequence =
                    for (v, ty) <- c.quantifiedVariables.zip(c.signature)
                    yield have((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN) |- in(v, getOrElse(ty, app(h, successor(n))))) by Weakening(liftHeight of (y := v))

                  val left = have((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN) |- constructorQuantVarsInHSuccN) by RightAnd(liftHeightAndSequence: _*)
                  val right = have(termWithQuantifiedVars === x |- termWithQuantifiedVars === x) by Hypothesis

                  have((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN, (termWithQuantifiedVars === x)) |- constructorQuantVarsInHSuccN /\ (termWithQuantifiedVars === x)) by RightAnd(
                    left,
                    right
                  )
                  thenHave((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN /\ (termWithQuantifiedVars === x)) |- constructorQuantVarsInHSuccN /\ (termWithQuantifiedVars === x)) by LeftAnd
                  thenHave((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN /\ (termWithQuantifiedVars === x)) |- isConstructorCXHSuccN) by QuantifiersIntro(c.quantifiedVariables)
                  thenHave((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorCXHSuccN) by QuantifiersIntro(c.quantifiedVariables)

                thenHave((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorXHSuccN) by Weakening

            have((hIsTheHeightFunction, in(n, N), isConstructorXHN) |- isConstructorXHSuccN) by LeftOr(liftConstructorHeightOrSequence: _*)

        // STEP 1.5: Show that x ∈ introductionFunction(height(n + 1)) => for some c, x = c(x1, ..., xn)
        // with xi, ..., xj ∈ height(n + 1).
        val heightSuccessorWeakForward = have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n)))) |- isInIntroductionFunctionImage(app(h, n))(x)) by Cut(
          heightSuccessorWeak,
          equivalenceApply of (p1 := in(x, app(h, successor(n))), p2 := isInIntroductionFunctionImage(app(h, n))(x))
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
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, heightSuccessorWeak.asInstanceOf)
    }

    /**
     * Generates the structural inductive case for a given constructor.
     *
     * @param c the constructor
     */
    lazy val structuralInductionPrecondition: Map[UntypedConstructor, Formula] = constructors
      .map(c =>
        c ->
          c.quantifiedVariables
            .zip(c.signature)
            .foldRight[Formula](P(c.termWithQuantifiedVars))((el, fc) =>
              val (v, ty) = el
              ty match
                case Self => forall(v, in(v, term) ==> (P(v) ==> fc))
                case t: Term => forall(v, in(v, t) ==> fc)
            )
      )
      .toMap

    /**
     * Theorem --- Structural induction principle for this ADT.
     *
     *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
     */
    lazy val structuralInduction = Lemma(constructors.foldRight[Formula](forall(x, in(x, term) ==> P(x)))((c, f) => structuralInductionPrecondition(c) ==> f)) {

      // List of cases to prove for structural induction to hold
      val structuralInductionPreconditions: Formula = /\(constructors.map(structuralInductionPrecondition))

      // We want to prove the claim by induction on the height of n, i.e. prove that for any
      // n in N, P holds.
      def inductionFormula(n: Term): Formula = forall(x, in(x, app(h, n)) ==> P(x))
      val inductionFormulaN: Formula = inductionFormula(n)

      // STEP 1: Prove the base case
      have(hIsTheHeightFunction |- in(x, app(h, emptySet)) ==> P(x)) by Weakening(heightZero)
      val baseCase = thenHave(hIsTheHeightFunction |- inductionFormula(emptySet)) by RightForall

      val inductiveCaseRemaining = have((hIsTheHeightFunction, forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n))))) |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(
        baseCase,
        natInduction of (P := lambda(n, inductionFormulaN))
      )

      // STEP 2: Prove the inductive case
      val inductiveCase = have((hIsTheHeightFunction, structuralInductionPreconditions) |- forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n))))) subproof {

        // STEP 2.1 : Prove that if the x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n) then P(x) holds.
        val isConstructorImpliesP = have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(x, app(h, n))) |- P(x)) subproof {

          if constructors.isEmpty then have(thesis) by Restate
          else
            val orSeq =
              (for c <- constructors yield

                // Caching
                val constructorPrecondition = structuralInductionPrecondition(c)
                val termWithQuantifiedVars = c.termWithQuantifiedVars
                val constructorQuantVarsInHN = constructorQuantifiedVarsInDomain(c, app(h, n))
                val constructorQuantVarsInHNEx = ∃(n, in(n, N) /\ constructorQuantifiedVarsInDomain(c, app(h, n)))
                val constructorQuantVarsInTerm = constructorQuantifiedVarsInDomain(c, term)

                // STEP 2.1.1: Prove that if xi, ..., xj ∈ height(n) then xi, ..., xj ∈ ADT.
                val constructorQuantVarsInHNToTerm = have((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN) |- constructorQuantVarsInTerm) subproof {
                  have((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN) |- in(n, N) /\ constructorQuantVarsInHN) by Restate
                  val consVarL = thenHave((hIsTheHeightFunction, in(n, N), constructorQuantVarsInHN) |- constructorQuantVarsInHNEx) by RightExists
                  have((constructorQuantVarsInTerm <=> constructorQuantVarsInHNEx, constructorQuantVarsInHNEx) |- constructorQuantVarsInTerm) by Restate.from(
                    equivalenceRevApply of (p1 := constructorQuantVarsInTerm, p2 := constructorQuantVarsInHNEx)
                  )
                  have((hIsTheHeightFunction, constructorQuantVarsInHNEx) |- constructorQuantVarsInTerm) by Cut(
                    termsHaveHeight(c).of(c.variables.zip(c.quantifiedVariables).map(_ := _): _*),
                    lastStep
                  )
                  have(thesis) by Cut(consVarL, lastStep)
                }

                // STEP 2.1.2: Prove that if xi, ..., xj ∈ height(n) then P(c(x1, ..., xn)).
                have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInHN) |- constructorPrecondition) by Restate

                c.quantifiedVariables
                  .zip(c.signature)
                  .foldLeft(lastStep)((fact, el) =>
                    val (v, ty) = el

                    fact.statement.right.head match
                      case Forall(_, factCclWithoutForall) =>
                        thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInHN) |- factCclWithoutForall) by InstantiateForall(v)

                        factCclWithoutForall match
                          case Implies(membership, subformula) =>
                            ty match
                              case Self =>
                                subformula match
                                  case Implies(hypothesis, subSubFormula) =>
                                    val proofSubSubFormula = thenHave(
                                      (hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInTerm, constructorQuantVarsInHN, P(v)) |- subSubFormula
                                    ) by Weakening

                                    have(inductionFormulaN |- inductionFormulaN) by Hypothesis
                                    thenHave(inductionFormulaN |- in(v, app(h, n)) ==> P(v)) by InstantiateForall(v)
                                    thenHave((inductionFormulaN, constructorQuantVarsInHN) |- P(v)) by Weakening

                                    have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInTerm, constructorQuantVarsInHN) |- subSubFormula) by Cut(
                                      lastStep,
                                      proofSubSubFormula
                                    )
                                    have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInHN) |- subSubFormula) by Cut(
                                      constructorQuantVarsInHNToTerm,
                                      lastStep
                                    )

                                  case _ => throw UnreachableException

                              case t: Term =>
                                thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInHN) |- subformula) by Restate
                          case _ => throw UnreachableException
                      case _ => throw UnreachableException
                  )

                thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInHN) |- P(termWithQuantifiedVars)) by Restate

                // STEP 2.1.3: Prove that if xi, ..., xj ∈ height(n) then P(x).
                thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInHN, termWithQuantifiedVars === x) |- P(x)) by RightSubstEq
                  .withParametersSimple(List((x, termWithQuantifiedVars)), lambda(x, P(x)))

                thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorQuantVarsInHN /\ (termWithQuantifiedVars === x)) |- P(x)) by LeftAnd

                thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, isConstructor(c, x, app(h, n))) |- P(x)) by QuantifiersIntro(c.quantifiedVariables)

                thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(c, x, app(h, n))) |- P(x)) by Weakening
              ).toSeq

            have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(x, app(h, n))) |- P(x)) by LeftOr(orSeq: _*)
        }

        // STEP 2.2: Prove that if x ∈ height(n + 1) then P(x) holds.
        have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n)))) |- isConstructor(x, app(h, n))) by Cut(
          heightSuccessorStrong,
          equivalenceApply of (p1 := in(x, app(h, successor(n))), p2 := isConstructor(x, app(h, n)))
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
      have((hIsTheHeightFunction, in(x, term)) |- exists(n, in(n, N) /\ in(x, app(h, n)))) by Cut(termHasHeight, equivalenceApply of (p1 := in(x, term), p2 := exists(n, in(n, N) /\ in(x, app(h, n)))))

      have((hIsTheHeightFunction, structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(lastStep, exImpliesP)
      thenHave((exists(h, hIsTheHeightFunction), structuralInductionPreconditions, in(x, term)) |- P(x)) by LeftExists
      have((structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(heightFunctionExistence, lastStep)
      thenHave(structuralInductionPreconditions |- in(x, term) ==> P(x)) by RightImplies
      thenHave(structuralInductionPreconditions |- forall(x, in(x, term) ==> P(x))) by RightForall
    }

  }

  class TypedConstructor(using line: sourcecode.Line, file: sourcecode.File)(val inner: UntypedConstructor, adt: UntypedADT) {

    /**
     * Full name of the constructor, i.e. concatenation of the ADT name and the constructor name.
     */
    val fullName: String = s"${adt.name}/${inner.name}"

    /**
     * Type variables that may appear in the signature of the constructor.
     */
    val typeVariables: Seq[Variable] = adt.typeVariables

    /**
     * Number of type variables that may appear in the signature of the constructor.
     */
    val typeArity: Int = typeVariables.length

    /**
     * Signature of the constructor.
     */
    val signature: Seq[Term] = inner.signature.map(getOrElse(_, adt.term))

    /**
     * Type of the constructor.
     */
    val typ: Term = signature.foldRight[Term](adt.term)((a, b) => a |=> b)

    /**
     * Set of variables to be used when reasonning about this constructor.
     */
    val variables: Seq[Variable] = inner.variables

    val variablesWellTyped: Set[Formula] = variables.zip(signature).map((v, t) => v :: t).toSet

    /**
     * Number of arguments of this constructor.
     */
    val arity: Int = inner.arity

    /**
     * Applies this constructor's terms variables on a function.
     *
     * @param f the function to apply the variables on
     */
    def appVars(f: Term): Term = appSeq(f)(variables)

    /**
     * Internal representation of this constructor.
     */
    private val structuralTerm: Term = inner.term

    /**
     * Definition of this constructor.
     *
     * Formally it is the only function whose codomain is the ADT such that for all variables x1 :: S1, ...,xn :: Sn
     * c(x1, ..., xn) = (tagc, (x1, (..., (xn, ∅)...))
     */
    private val untypedFunctionalDefinition = (c :: typ) /\ forallSeq(variables, 
      variables.zip(signature).foldRight(appVars(c) === structuralTerm)((el, acc) =>
          (el._1 :: el._2) ==> acc
      ))

    /**
     * Lemma --- Uniqueness of this constructor.
     *
     *     ` ∃!c. c ∈ T1 -> ... -> Tn -> ADT /\ ∀x1, ..., xn. c(x1, ..., xn) = (tagc, (x1, (..., (xn, ∅)...))`
     */
    val untypedFunctionalUniqueness = Axiom(existsOne(c, untypedFunctionalDefinition))

    /**
     * Set theoretic definition of the constructor.
     */
    private val untypedFunctional = FunctionDefinition(fullName, line.value, file.value)(typeVariables, c, untypedFunctionalDefinition, untypedFunctionalUniqueness).label

    /**
     * Constructor where type variables are instantiated with schematic symbols.
     */
    val term = untypedFunctional.applySeq(typeVariables)

    /**
     * Constructor where type and term variables are instantiated with schematic symbols.
     */
    val appliedTerm = appVars(term)

    /**
     * Lemma --- This constructor is equal to its internal representation.
     *
     *     `∀x1, ..., xn. c(x1, ..., xn) = (tagc, (x1, (..., (xn, ∅)...))`
     */
    val shortDefinition = Lemma(forallSeq(variables, variables.zip(signature).foldRight(appVars(term) === structuralTerm)((el, acc) =>
      (el._1 :: el._2) ==> acc))) {
      have(forall(c, (term === c) <=> ((c :: typ) /\ forallSeq(variables, variables.zip(signature).foldRight(appVars(c) === structuralTerm)((el, acc) =>
      (el._1 :: el._2) ==> acc))))) by Exact(untypedFunctional.definition)
      thenHave((term === term) <=> ((term :: typ) /\ forallSeq(variables, variables.zip(signature).foldRight(appVars(term) === structuralTerm)((el, acc) =>
      (el._1 :: el._2) ==> acc)))) by InstantiateForall(term)
      thenHave(thesis) by Weakening
    }

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
     *
     * e.g. Cons(head1, tail1) === Cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
     */
    lazy val injectivity = 
      // variable sequences x_0, ..., x_n-1 and y_0, ..., y_n-1
      val vars1 = variables
      val vars2 = inner.quantifiedVariables
      val tappterm1 = appSeq(term)(vars1)
      val tappterm2 = appSeq(term)(vars2)

      val vars1WellTyped: Set[Formula] = variablesWellTyped
      val vars2WellTyped: Set[Formula] = vars2.zip(signature).map((v, t) => v :: t).toSet

      if inner.arity == 0 then
        Lemma(tappterm1 === tappterm2) {
          have(thesis) by RightRefl
        }
      else
        Lemma(vars1WellTyped ++ vars2WellTyped |- simplify((tappterm1 === tappterm2) <=> /\(vars1.zip(vars2).map(_ === _)))) {

          val txs = inner.term(vars1)
          val tys = inner.term(vars2)

          val tappFunDef = have(forallSeq(variables, variables.zip(signature).foldRight(appVars(term) === structuralTerm)((el, acc) =>
      (el._1 :: el._2) ==> acc))) by Restate.from(shortDefinition)

          vars1
            .zip(inner.variables)
            .foldLeft(tappFunDef)((fact, p) =>
              val (x, v) = p
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi.substitute(v := x)) by InstantiateForall(x)
                case _ => throw UnreachableException
            )
          val tappTerm1Def = thenHave(vars1WellTyped |- tappterm1 === txs) by Restate

          have(tappFunDef.statement) by Restate.from(tappFunDef)

          vars2
            .zip(inner.variables)
            .foldLeft(tappFunDef)((fact, p) =>
              val (y, v) = p
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi.substitute(v := y)) by InstantiateForall(y)
                case _ => throw UnreachableException
            )
          val tappTerm2Def = thenHave(vars2WellTyped |- tappterm2 === tys) by Restate


          val s0 = have(vars2WellTyped + (tappterm1 === tappterm2) |- tappterm1 === tys) by Cut(tappTerm2Def,
            altEqualityTransitivity of (x := tappterm1, y := tappterm2, z := tys))
          have(vars1WellTyped + (tappterm1 === tys) |- txs === tys) by Cut(tappTerm1Def,
            altEqualityTransitivity of (x := txs, y := tappterm1, z := tys))
          have((vars1WellTyped ++ vars2WellTyped) + (tappterm1 === tappterm2) |- txs === tys) by Cut(s0, lastStep)
          val forward = thenHave(vars1WellTyped ++ vars2WellTyped |- (tappterm1 === tappterm2) ==> (txs === tys)) by RightImplies

          val s1 = have(vars1WellTyped + (txs === tys) |- tappterm1 === tys) by Cut(tappTerm1Def,
            altEqualityTransitivity of (x := tappterm1, y := txs, z := tys))
          have(vars2WellTyped + (tappterm1 === tys) |- tappterm1 === tappterm2) by Cut(tappTerm2Def,
            altEqualityTransitivity of (x := tappterm1, y := tys, z := tappterm2))
          have((vars1WellTyped ++ vars2WellTyped) + (txs === tys) |- tappterm1 === tappterm2) by Cut(s1, lastStep)
          val backward = thenHave(vars1WellTyped ++ vars2WellTyped |- (txs === tys) ==> (tappterm1 === tappterm2)) by RightImplies

          val definitionUnfolding = have(vars1WellTyped ++ vars2WellTyped |- (tappterm1 === tappterm2) <=> (txs === tys)) by RightIff(forward, backward)
          have((tappterm1 === tappterm2) <=> (txs === tys) |- (tappterm1 === tappterm2) <=> /\(vars1.zip(vars2).map(_ === _))) by Sorry
          Cut(
            inner.injectivity,
            equivalenceRewriting of (p1 := (tappterm1 === tappterm2), p2 := (txs === tys), p3 := /\(vars1.zip(vars2).map(_ === _)))
          )
          have(thesis) by Cut(definitionUnfolding, lastStep)
        }

    /**
     * Typing rule of the constructor.
     */
    val typing = Lemma(forallSeq(typeVariables, term :: typ)) {
      have(forall(c, (term === c) <=> ((c :: typ) /\ forallSeq(variables, variables.zip(signature).foldRight(appVars(c) === structuralTerm)((el, acc) =>
      (el._1 :: el._2) ==> acc))))) by Exact(untypedFunctional.definition)
      thenHave((term === term) <=> ((term :: typ) /\ forallSeq(variables, variables.zip(signature).foldRight(appVars(term) === structuralTerm)((el, acc) =>
      (el._1 :: el._2) ==> acc)))) by InstantiateForall(term)
      thenHave(term :: typ) by Weakening
      thenHave(thesis) by QuantifiersIntro(typeVariables)
    }

    /**
     * @see [[this.typing]]
     */
    val intro = typing

    /**
     * Type theoretic definition of the constructor.
     */
    private val typedFunctional = TypedConstantFunctional(fullName, typeArity, FunctionalClass(Seq.fill(typeArity)(any), typeVariables, typ, typeArity), typing)

    def apply(terms: Term*) = typedFunctional.applySeq(terms)

  }

  class TypedADT(private val inner: UntypedADT, val constructors: Seq[TypedConstructor]) {

    /**
     * Type variables of this ADT.
     */
    private val typeVariables: Seq[Variable] = inner.typeVariables

    /**
     * Instantiates the type variables of this ADT with the given terms.
     *
     * @param args the arguments to instantiate the type variables with
     */
    def apply(args: Term*) =
      require(args.length == typeVariables.length, "The number of arguments must match the number of type variables.")
      inner.polymorphicTerm.applySeq(args)

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of different construcors are always different.
     *
     * e.g. Nil != Cons(head, tail)
     */
    def injectivity(c1: TypedConstructor, c2: TypedConstructor) =
      require(c1.inner.tag != c2.inner.tag, "The given constructors must be different.")

      val appliedTerm1 = c1.appliedTerm
      val appliedTerm2 = appSeq(c2.term)(c2.inner.quantifiedVariables)
      val t1 = c1.inner.term
      val t2 = c2.inner.termWithQuantifiedVars
      val tagTerm1 = c1.inner.tagTerm
      val tagTerm2 = c2.inner.tagTerm
      val vars1WellTyped: Set[Formula] = c1.variablesWellTyped
      val vars2WellTyped: Set[Formula] = c2.inner.quantifiedVariables.zip(c2.signature).map((v, t) => v :: t).toSet

      Lemma(vars1WellTyped ++ vars2WellTyped |- !(appliedTerm1 === appliedTerm2)) {

        val diffTag = have(!(tagTerm1 === tagTerm2)) subproof {
          val tag1 = c1.inner.tag
          val tag2 = c2.inner.tag

          val minTag: Int = Math.min(tag1, tag2)
          val maxTag: Int = Math.max(tag1, tag2)

          val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Restate

          (1 to minTag).foldLeft(start)((fact, i) =>
            val midMaxTag = toTerm(maxTag - i)
            val midMinTag = toTerm(minTag - i)
            have(successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag) by Cut(
              successorInjectivity of (n := midMaxTag, m := midMinTag),
              equivalenceApply of (p1 := successor(midMaxTag) === successor(midMinTag), p2 := midMaxTag === midMinTag)
            )
            have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
          )

          val chainInjectivity = thenHave(!(toTerm(maxTag - minTag) === emptySet) |- !(tagTerm1 === tagTerm2)) by Restate

          have(!(toTerm(maxTag - minTag) === emptySet)) by Exact(zeroIsNotSucc)
          have(!(tagTerm1 === tagTerm2)) by Cut(lastStep, chainInjectivity)
        }

        val defUnfolding = have((vars1WellTyped ++ vars2WellTyped) + (appliedTerm1 === appliedTerm2) |- t1 === t2) subproof {
          have(forallSeq(c1.variables, c1.variables.zip(c1.signature).foldRight(appliedTerm1 === t1)((el, acc) =>
      (el._1 :: el._2) ==> acc))) by Restate.from(c1.shortDefinition)

          c1.variables.foldLeft(lastStep)((fact, v) =>
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi.substitute(v := x)) by InstantiateForall(x)
              case _ => throw UnreachableException
          )
          val tappTerm1Def = thenHave(vars1WellTyped |- t1 === appliedTerm1) by Restate

          have(forallSeq(c2.inner.quantifiedVariables, c2.inner.quantifiedVariables.zip(c2.signature).foldRight(appliedTerm2 === t2)((el, acc) =>
                (el._1 :: el._2) ==> acc))) by Restate.from(c2.shortDefinition)

          c2.inner.quantifiedVariables.foldLeft(lastStep)((fact, v) =>
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException
          )
          val tappTerm2Def = thenHave(vars2WellTyped |- appliedTerm2 === t2) by Restate

          val s0 = have(vars2WellTyped + (appliedTerm1 === appliedTerm2) |- appliedTerm1 === t2) by Cut(
            tappTerm2Def,
            altEqualityTransitivity of (x := appliedTerm1, y := appliedTerm2, z := t2)
          )
          have(vars1WellTyped + (appliedTerm1 === t2) |- t1 === t2) by Cut(
            tappTerm1Def,
            altEqualityTransitivity of (x := t1, y := appliedTerm1, z := t2)
          )
          have(thesis) by Cut(s0, lastStep)
        }

        have(t1 === t2 |- (tagTerm1 === tagTerm2) /\ (c1.inner.subterm === c2.inner.subtermWithQuantifiedVars)) by Apply(equivalenceRevApply).on(
          pairExtensionality of (a := tagTerm1, b := c1.inner.subterm, c := tagTerm2, d := c2.inner.subtermWithQuantifiedVars)
        )
        thenHave(!(tagTerm1 === tagTerm2) |- !(t1 === t2)) by Weakening

        have(!(t1 === t2)) by Cut(diffTag, lastStep)
        thenHave(t1 === t2 |- ()) by Restate

        have((vars1WellTyped ++ vars2WellTyped) + (appliedTerm1 === appliedTerm2) |- ()) by Cut(defUnfolding, lastStep)
      }

    /**
     * Generates the inductive case for every constructor.
     */
    private lazy val inductionPrecondition: Map[TypedConstructor, Formula] = constructors
      .map(c =>
        c ->
          c.variables
            .zip(c.inner.signature)
            .foldRight[Formula](P(c.appVars(c.term)))((el, fc) =>
              val (v, ty) = el
              ty match
                case Self => forall(v, v :: inner.term ==> (P(v) ==> fc))
                case t: Term => forall(v, v :: t ==> fc)
            )
      )
      .toMap

    /**
     * Theorem --- Structural induction principle for this ADT.
     *
     *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
     */
    lazy val induction = Lemma(constructors.foldRight[Formula](forall(x, x :: inner.term ==> P(x)))((c, f) => inductionPrecondition(c) ==> f)) { sp ?=>
      constructors.foldRight[(Formula, Formula, sp.Fact)] {
        val before = forall(x, in(x, inner.term) ==> P(x))
        val after = forall(x, x :: inner.term ==> P(x))
        (before, after, have(before <=> after) by Restate)
      }((c, acc) =>
        val (oldBefore, oldAfter, fact) = acc
        val newBefore = inner.structuralInductionPrecondition(c.inner) ==> oldBefore
        val newAfter = inductionPrecondition(c) ==> oldAfter

        have(inner.structuralInductionPrecondition(c.inner) <=> inductionPrecondition(c)) subproof {
          val outerTerm = appSeq(c.term)(c.inner.quantifiedVariables)
          val quantifiedVariablesWellTypedSeq: Seq[Formula] = c.inner.quantifiedVariables.zip(c.signature).map((v, t) => v :: t)
          val quantifiedVariablesWellTyped = quantifiedVariablesWellTypedSeq.toSet


          have(forallSeq(c.inner.quantifiedVariables, c.inner.quantifiedVariables.zip(c.signature).foldRight(appSeq(c.term)(c.inner.quantifiedVariables) === c.inner.termWithQuantifiedVars)((el, acc) =>
      (el._1 :: el._2) ==> acc))) by Restate.from(c.shortDefinition)
          if c.arity > 0 then
            c.inner.variables.foldLeft(lastStep)((l, _) =>
              lastStep.statement.right.head match
                case Forall(v, phi) => thenHave(phi) by InstantiateForall(v)
                case _ => throw UnreachableException
            )

          val eq = thenHave(quantifiedVariablesWellTyped |- outerTerm === c.inner.termWithQuantifiedVars) by Restate
          have(P(outerTerm) <=> P(outerTerm)) by Restate
          thenHave(c.inner.termWithQuantifiedVars === outerTerm |- P(c.inner.termWithQuantifiedVars) <=> P(outerTerm)) by RightSubstEq.withParametersSimple(
            List((c.inner.termWithQuantifiedVars, outerTerm)),
            lambda(s, P(c.inner.termWithQuantifiedVars) <=> P(s))
          )
          have(quantifiedVariablesWellTyped |- P(c.inner.termWithQuantifiedVars) <=> P(outerTerm)) by Cut(eq, lastStep)

          c.inner.quantifiedVariables
            .zip(c.inner.signature)
            .foldRight[(Formula, Formula, Seq[Formula])]((P(c.inner.termWithQuantifiedVars), P(outerTerm), quantifiedVariablesWellTypedSeq))((el, fc) =>
              val (v, ty) = el
              val (fc1, fc2, wellTypedVars) = fc
              ty match
                case Self =>
                  have(wellTypedVars |- (P(v) ==> fc1) <=> (P(v) ==> fc2)) by Cut(lastStep, leftImpliesEquivalence of (p := P(v), p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- (in(v, inner.term) ==> (P(v) ==> fc1)) <=> (v :: inner.term ==> (P(v) ==> fc2))) by Tautology
                  // Cut(
                  //   lastStep,
                  //   leftImpliesEquivalence of (p := in(v, inner.term), p1 := P(v) ==> fc1, p2 := P(v) ==> fc2)
                  // )
                  thenHave(wellTypedVars.init |- forall(v, (in(v, inner.term) ==> (P(v) ==> fc1)) <=> (v :: inner.term ==> (P(v) ==> fc2)))) by RightForall
                  have(wellTypedVars.init |- forall(v, (in(v, inner.term) ==> (P(v) ==> fc1))) <=> forall(v, (v :: inner.term ==> (P(v) ==> fc2)))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, in(v, inner.term) ==> (P(v) ==> fc1)), Q := lambda(v, v :: inner.term ==> (P(v) ==> fc2)))
                  )
                  (forall(v, in(v, inner.term) ==> (P(v) ==> fc1)), forall(v, v :: inner.term ==> (P(v) ==> fc2)), wellTypedVars.init)
                case t: Term =>
                  thenHave(wellTypedVars.init |- (in(v, t) ==> fc1) <=> (v :: t ==> fc2)) by Tautology//Cut(lastStep, leftImpliesEquivalence of (p := in(v, t), p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- forall(v, (in(v, t) ==> fc1) <=> (v :: t ==> fc2))) by RightForall
                  have(wellTypedVars.init |- forall(v, (in(v, t) ==> fc1)) <=> forall(v, (v :: t ==> fc2))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, in(v, t) ==> fc1), Q := lambda(v, v :: t ==> fc2))
                  )
                  (forall(v, (in(v, t) ==> fc1)), forall(v, (v :: t ==> fc2)), wellTypedVars.init)
            )
        }
        (newBefore, newAfter, have(newBefore <=> newAfter) by Apply(impliesEquivalence).on(lastStep, fact))
      )
      have(inner.structuralInduction.statement.right.head |- thesis.right.head) by Cut(
        lastStep,
        equivalenceApply of (
          p1 := inner.structuralInduction.statement.right.head, p2 := thesis.right.head
        )
      )
      have(thesis) by Cut(inner.structuralInduction, lastStep)
    }

    /**
      * Returns a map binding each constructor to formula describing whether x is an instance of it.
      */
    private lazy val isConstructorMap: Map[TypedConstructor, Formula] =
      constructors.map(c => c -> existsSeq(c.variables, /\((c.variables.zip(c.signature).map((v, t) => v :: t))) /\ (x === appSeq(c.term)(c.variables)))).toMap

    /**
      * Returns a formula describing whether x is an instance of one of this ADT's constructors.
      */
    private lazy val isConstructor =
      \/(constructors.map(c => isConstructorMap(c)))

    /**
     * Theorem --- Pattern matching principle (also known as elimination rule) for this ADT.
     *
     *    `x ∈ ADT |- x = c(x1, ..., xn) for some constructor c and xi, ..., xj ∈ ADT`
     */
    lazy val patternMatching = Lemma(x :: inner.term |- simplify(isConstructor)) {

      // Induction preconditions with P(z) = z != x
      val inductionPreconditionIneq = inductionPrecondition.map((c, f) => c -> f.substitute((P -> lambda(z, !(x === z)))))
      val inductionPreconditionsIneq = /\(inductionPreconditionIneq.map(_._2))

      // Weakening of the negation of the induction preconditions
      val weakNegInductionPreconditionIneq: Map[TypedConstructor, Formula] = constructors
        .map(c =>
          c ->
            c.variables
              .zip(c.signature)
              .foldRight[Formula](appSeq(c.term)(c.variables) === x)((el, fc) =>
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
                have(x === appSeq(c.term)(c.variables) |- x === appSeq(c.term)(c.variables)) by Hypothesis

                c.variables
                  .zip(c.inner.signature)
                  .foldRight(lastStep)((el, fact) =>
                    val (v, ty) = el
                    val left = fact.statement.left.head
                    val right = fact.statement.right.head

                    ty match
                      case Self =>
                        thenHave(!(x === v) /\ left |- right) by Weakening
                      case _ => ()

                    val weakr = thenHave(in(v, getOrElse(ty, inner.term)) /\ left |- right) by Weakening
                    val weakl = have(in(v, getOrElse(ty, inner.term)) /\ left |- in(v, getOrElse(ty, inner.term))) by Restate

                    have((v :: getOrElse(ty, inner.term)) /\ left |- (v :: getOrElse(ty, inner.term)) /\ right) by RightAnd(weakl, weakr)
                    thenHave((v :: getOrElse(ty, inner.term)) /\ left |- exists(v, (v :: getOrElse(ty, inner.term)) /\ right)) by RightExists
                    thenHave(exists(v, (v :: getOrElse(ty, inner.term)) /\ left) |- exists(v, (v :: getOrElse(ty, inner.term)) /\ right)) by LeftExists
                  )

              }

              // STEP 1.1.2: Conclude
              // TODO: Change to a more efficient way of proving this
              have(weakNegInductionPreconditionIneq(c) |- isConstructorMap(c)) by Tableau
              have(!inductionPreconditionIneq(c) |- isConstructorMap(c)) by Cut(conditionStrenghtening, lastStep)
              thenHave(!inductionPreconditionIneq(c) |- isConstructor) by Weakening

          have(thesis) by LeftOr(negInductionPreconditionsOrSequence: _*)
      }

      // STEP 2: Conclude
      have(inductionPreconditionsIneq |- forall(z, z :: inner.term ==> !(x === z))) by Restate.from(induction of (P := lambda(z, !(x === z))))
      thenHave(inductionPreconditionsIneq |- x :: inner.term ==> !(x === x)) by InstantiateForall(x)
      val ind = thenHave(x :: inner.term |- !inductionPreconditionsIneq) by Restate
      have(x :: inner.term |- isConstructor) by Cut(lastStep, strengtheningOfInductionPreconditions)
    }

    /**
      * @see [[this.patternMatching]]
      */
    lazy val elim = patternMatching

  }


  /**
    * Companion object for the [[TypedADT]] class.
    */
  object TypedADT {

    /**
      * Generate an ADT and a list of constructors from a user specification
      *
      * @param name name of the ADT
      * @param untypedConstructors user specification for each constructor
      */
    def apply(name: String, untypedConstructors: Seq[UntypedConstructor]): TypedADT =
      val untypedADT = new UntypedADT(name, untypedConstructors)
      new TypedADT(untypedADT, untypedConstructors.map(TypedConstructor(_, untypedADT)))

  }

  /**
   * This object provides a DSL for defining algebraic data types (ADTs) in Lisa.
   *
   * This is an example of ADT definition in Lisa
   * {{{
   * val define(list: ADT, constructors(nil, cons)) = () | (x, list)
   * }}}
   * where `list`, `nil` and `cons` are new identifiers freely chosen by the user, referring respectively to the generated ADT
   * and its constructors, and `x` is a term variable.
   *
   * Formally, we define an ADT as a sequence of tuples where each tuple represents the signature of a constructor. Each tuple can either contain:
   * - a constant term (e.g. `emptySet`, or `pair(emptySet, emptySet)`)
   * - a term variable (e.g. `x`)
   * - a reference to the adt itself by using the identifier that the user is giving to the ADT (e.g. `myadt`)
   *
   * The syntax then consists of
   * {{{
   * val defined(idGivenToTheADT: ADT, constuctors(idGivenToFirstConstructor, ..., idGivenToLastConstructor)) = * tuple sequence *
   * }}}
   *
   * The user can then freely refer to the identifiers of the ADT and constructors in the rest of the program.
   * The identifer given to the ADT is of type [[TypedADT]] while the identifiers given to the constructors are of type [[TypedConstructor]].
   */
  object ADTSyntax {

    /**
     * Builder for defining the signature of a constructor.
     *
     * @param param the parameters of the constructor
     */
    case class ConstructorBuilder(private val param: Seq[ConstructorArgument]) {

      /**
       * Merges the parameters of two constructors.
       *
       * @param b the other constructor
       */
      infix def ++(b: ConstructorBuilder): ConstructorBuilder = ConstructorBuilder(param ++ b.param.toSeq)

      /**
       * Converts this constructor into an ADT with a single constructor.
       */
      def toADTBuilder = ADTBuilder(Seq(this))

      /**
       * Combines two constructors into an ADT.
       *
       * @param b the other constructor
       */
      infix def |(b: ConstructorBuilder): ADTBuilder = this | b.toADTBuilder

      /**
       * Adds this constructor to an ADT.
       *
       * @param b the ADT to which the constructor is added
       */
      infix def |(b: ADTBuilder): ADTBuilder = toADTBuilder | b

      /**
       * Outputs the [[UntypedConstructor]] associated with this builder.
       *
       * @param name the name of the constructor
       */
      def build(name: String): UntypedConstructor = UntypedConstructor(name, param)
    }

    /**
     *  Companion object for the [[ConstructorBuilder]] class.
     */
    object ConstructorBuilder {

      /**
       * Creates an empty [[ConstructorBuilder]].
       */
      def empty: ConstructorBuilder = ConstructorBuilder(Seq.empty)
    }

    protected trait ConstructorConverter[-T] {

      /**
       * Converts a value into a [[ConstructorBuilder]].
       */
      def apply(t: T): ConstructorBuilder
    }

    /**
     * Converts a value into a [[ConstructorBuilder]].
     *
     * @param any the value to convert
     * @param c the converter that is used for the conversion
     */
    def any_to_const[T](any: T)(using c: ConstructorConverter[T]): ConstructorBuilder = c(any)

    given unit_to_const[U <: Unit]: ConstructorConverter[U] with {

      /**
       * Converts a unit value into a constructor taking no arguments.
       */
      override def apply(u: U): ConstructorBuilder = ConstructorBuilder.empty
    }

    given empty_to_const[E <: EmptyTuple]: ConstructorConverter[E] with {

      /**
       * Converts an empty tuple into a constructor taking no arguments.
       */
      override def apply(t: E): ConstructorBuilder = ConstructorBuilder.empty
    }

    given term_to_const[T <: Term]: ConstructorConverter[T] with {

      /**
       * Converts a term into a constructor taking one non inductive argument.
       */
      override def apply(t: T): ConstructorBuilder = ConstructorBuilder(Seq(t))
    }

    given adt_to_const[A <: ADT]: ConstructorConverter[A] with {

      /**
       * Converts an ADT into a constructor taking one inductive argument.
       */
      override def apply(a: A): ConstructorBuilder = ConstructorBuilder(Seq(Self))
    }

    given tuple_to_const[H <: ADT | Term, T <: Tuple]: ConstructorConverter[H *: T] with {

      /**
       * Converts a tuple prepended with a type into a constructor taking an argument and whose other arguments are deduced from
       * applying recursively the conversion to the tuple.
       */
      override def apply(t: H *: T): ConstructorBuilder =
        any_to_const(t.head)(using
          // If the value is null then it is a self reference and hence the type is ADT, otherwise it is term
          // The way this conversion is achieved is very hacking but I did not find a better way to do it
          Option(t.head) match
            case None => adt_to_const.asInstanceOf[ConstructorConverter[H]]
            case Some(_) => term_to_const.asInstanceOf[ConstructorConverter[H]]
        ) ++ any_to_const(t.tail)(using
          t.tail match
            case _: EmptyTuple => empty_to_const.asInstanceOf[ConstructorConverter[T]]
            case _ => tuple_to_const.asInstanceOf[ConstructorConverter[T]]
        )
    }

    extension [T1](left: T1)(using c1: ConstructorConverter[T1])
      /**
       * Converts two values into constructors and combines them into an ADT.
       *
       * @param right the other value to convert
       * @param c2 the implicit converter for the second value
       */
      infix def |[T2](right: T2)(using c2: ConstructorConverter[T2]): ADTBuilder = any_to_const(left) | any_to_const(right)

    case class ADTBuilder(private val constructors: Seq[ConstructorBuilder]) {

      /**
       * The number of constructors in the ADT.
       */
      def size: Int = constructors.length

      /**
       * Combines this ADT with another one.
       *
       * @param b the other ADT
       */
      infix def |(b: ADTBuilder): ADTBuilder = ADTBuilder(constructors ++ b.constructors)

      /**
       * Adds a constructor to this ADT.
       *
       * @param b the constructor to add
       */
      infix def |(b: ConstructorBuilder): ADTBuilder = this | b.toADTBuilder

      /**
       * Converts a value into a constructor and adds it to this ADT.
       *
       * @param t the value to convert
       * @param c the implicit converter
       */
      infix def |[T](t: T)(using c: ConstructorConverter[T]): ADTBuilder = this | any_to_const(t)

      /**
       * Outputs the constructors of this ADT.
       *
       * @param names the names of the constructors
       */
      def build(names: Seq[String]): Seq[UntypedConstructor] =
        val trimmedNames = names.take(size)
        require(
          trimmedNames.length == constructors.length,
          s"The number of new identifiers for constructors must match the given specification.\nNew identifiers: ${names.length}, number of constructors: ${constructors.length}."
        )
        constructors.zip(names).map(_.build(_))

    }

    /**
     *  Companion object for the [[ADTBuilder]] class.
     */
    object ADTBuilder {

      /**
       * Creates an empty [[ADTBuilder]].
       */
      def empty: ADTBuilder = ADTBuilder(Seq.empty)
    }



    type ADT = TypedADT

    /**
      * Lists all constructors of this ADT.
      */
    case class constructors(c: TypedConstructor*)


    object define {

      import scala.quoted._

      inline def extractNames[T](e: T): Seq[String] = ${extractNames('{e})}

      def extractNames[T](using Quotes)(e: Expr[T]) : Expr[Seq[String]]  =

        import quotes.reflect._

        val subscope = Symbol.spliceOwner.owner.owner.owner.owner
        val scope = subscope.owner
        val tree = scope.tree

        case class traverser(s: Symbol) extends TreeTraverser {
          var reachedADT: Boolean = false 
          var constructorNames: Seq[String] = Seq.empty[String]

          override def traverseTree(tree: Tree)(owner: Symbol): Unit = tree match 
            case v : ValDef => 
              if !reachedADT then
                if v.symbol == s then
                  constructorNames = constructorNames :+ v.symbol.name
                  reachedADT = true
              else
                constructorNames = constructorNames :+ v.symbol.name

              super.traverseTree(tree)(owner)
            case _ => super.traverseTree(tree)(owner)
        }

        val trav = traverser(subscope)
        trav.traverseTree(tree)(scope)
        Expr(trav.constructorNames)

      private def extractConstructors(adt: TypedADT): (TypedADT, constructors) = (adt, constructors(adt.constructors : _*))

      inline def unapply(builder: ADTBuilder): (TypedADT, constructors) =
        val names = extractNames(builder)
        if builder.size == 0 then
          extractConstructors(TypedADT(names.head, builder.build(Seq.empty)))
        else
          extractConstructors(TypedADT(names.tail.head, builder.build(names.tail.tail)))

      inline def unapply(builder: ConstructorBuilder): (TypedADT, constructors) = unapply(builder.toADTBuilder)

      inline def unapply(v: Term): (TypedADT, constructors) = unapply(term_to_const(v))

      inline def unapply(inline v: Unit): (TypedADT, constructors) = unapply(unit_to_const(v))


      inline def unapply(v: ADT): (TypedADT, constructors) = unapply(adt_to_const(v))
      inline def unapply(n: None.type): (TypedADT, constructors) = unapply(ADTBuilder.empty)
      inline def unapply(v: EmptyTuple): (TypedADT, constructors) = unapply(empty_to_const(v))
      inline def unapply[H <: ADT | Term, T <: Tuple](v: H *: T): (TypedADT, constructors) = unapply(tuple_to_const(v))
    }

  }
}

/**
 * List of external set theoretic theorems needed for proofs below.
 * Some of these theorems are not yet implemented in the library and
 * will be added in the future.
 */
object ADTHelperTheorems extends lisa.Main {

  import ADTHelperDefinitions.*

  // *************************
  // * VARIABLES DECLARATION *
  // *************************

  val a = variable
  val b = variable
  val c = variable
  val d = variable

  val f = variable
  val g = variable
  val h = variable

  val n = variable
  val m = variable

  val p = formulaVariable
  val p1 = formulaVariable
  val p2 = formulaVariable
  val p3 = formulaVariable
  val p4 = formulaVariable

  val q1 = formulaVariable
  val q2 = formulaVariable

  val r = variable
  val s = variable
  val t = variable

  val x = variable
  val y = variable
  val z = variable

  val Q = predicate[1]
  val P = predicate[1]
  val P2 = predicate[2]

  // *********************
  // * FIRST ORDER LOGIC *
  // *********************


  /**
    * Lemma --- Alternative statement of transitivity of equality.
    */
  val altEqualityTransitivity = Lemma((x === y, y === z) |- x === z) {
    have(thesis) by Restate.from(equalityTransitivity)
  }

  /**
   * Lemma --- Transitivity of equivalence.
   */
  val equivalenceRewriting = Lemma((p1 <=> p2, p2 <=> p3) |- p1 <=> p3) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- Modus ponens for equivalence.
   */
  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- Top level existential quantifiers can be swapped.
   */
  val existentialSwap = Lemma(∃(x, ∃(y, P2(x, y))) <=> ∃(y, ∃(x, P2(x, y)))) {
    have(thesis) by Tableau
  }

  /**
   * Lemma --- Modus ponens for reversed equivalence.
   */
  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If a statement is equivalent to the conjunction of two other statements, and one of them is true, then it can be removed from the equivalence.
   */
  val equivalenceAnd = Lemma((p2, p1 <=> (p2 /\ p3)) |- p1 <=> p3) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If two formulas are equivalent then adding a disjunction on their right side preserves the equivalence.
   */
  val rightAndEquivalence = Lemma(p1 <=> p2 |- (p1 /\ p) <=> (p2 /\ p)) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If two formulas are equivalent then adding an implication on their left side preserves the equivalence.
   */
  val impliesEquivalence = Lemma((p1 <=> p2, p3 <=> p4) |- (p1 ==> p3) <=> (p2 ==> p4)) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If two formulas are equivalent then adding an implication on their left side preserves the equivalence.
   */
  val leftImpliesEquivalence = Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2)) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If there exists a unique element satisfying a predicate, then all
   * other elements satisfying the predicate are equal to it.
   */
  val existsOneUniqueness = Lemma((∃!(x, P(x)), P(x), P(y)) |- x === y) {
    sorry
  }

  // *******************
  // * NATURAL NUMBERS *
  // *******************

  // Natural numbers
  val N = Constant("N")
  addSymbol(N)

  /**
   * Lemma --- 0 is a natural number.
   *
   *    `0 ∈ N`
   */
  val zeroIsNat = Lemma(in(emptySet, N)) {
    sorry
  }

  /**
   * Lemma --- The natural numbers are not empty.
   *
   *   `N != ∅`
   */
  val natNotEmpty = Lemma(!(N === emptySet)) {
    have(thesis) by Cut(zeroIsNat, setWithElementNonEmpty of (y := emptySet, x := N))
  }

  /**
   * Lemma --- There exists a natural number.
   *
   *  `∃n ∈ N`
   */
  val existsNat = Lemma(exists(n, in(n, N))) {
    have(thesis) by RightExists(zeroIsNat)
  }

  /**
   * Lemma --- Successor is an injective function.
   *
   *   `n = m <=> n + 1 = m + 1`
   */
  val successorInjectivity = Lemma((n === m) <=> (successor(n) === successor(m))) {
    sorry
  }

  /**
   * Lemma --- A term is a natural number if and only if its successor is a natural number.
   *
   *  `n ∈ N <=> n + 1 ∈ N`
   */
  val successorIsNat = Lemma(in(n, N) <=> in(successor(n), N)) {
    sorry
  }

  /**
   * Lemma --- Any number is smaller than its successor
   *
   *     `∀n ∈ N. n < n + 1`
   */
  val inSuccessor = Lemma(in(n, successor(n))) {
    val uniomAxiomForward = have(exists(y, in(y, unorderedPair(n, singleton(n))) /\ in(n, y)) |- in(n, union(unorderedPair(n, singleton(n))))) by Cut(
      unionAxiom of (x := unorderedPair(n, singleton(n)), z := n),
      equivalenceRevApply of (p1 := exists(y, in(y, unorderedPair(n, singleton(n))) /\ in(n, y)), p2 := in(n, union(unorderedPair(n, singleton(n)))))
    )
    have(in(singleton(n), unorderedPair(n, singleton(n))) /\ in(n, singleton(n))) by RightAnd(
      secondElemInPair of (x := n, y := singleton(n)),
      singletonHasNoExtraElements of (x := n, y := n)
    )
    thenHave(exists(y, in(y, unorderedPair(n, singleton(n))) /\ in(n, y))) by RightExists
    have(in(n, union(unorderedPair(n, singleton(n))))) by Cut(lastStep, uniomAxiomForward)
    thenHave(union(unorderedPair(n, singleton(n))) === successor(n) |- in(n, successor(n))) by RightSubstEq.withParametersSimple(
      List((union(unorderedPair(n, singleton(n))), successor(n))),
      lambda(s, in(n, s))
    )
    have(thesis) by Cut(successor.shortDefinition of (x := n), lastStep)
  }

  /**
   * Lemma --- 0 is not the successor of any natural number.
   *
   *     `∀n ∈ N. n + 1 != 0`
   */
  val zeroIsNotSucc = Lemma(!(successor(n) === emptySet)) {
    have(thesis) by Cut(inSuccessor, setWithElementNonEmpty of (y := n, x := successor(n)))
  }

  /**
   * Lemma --- A number is smaller or equal than another number if and only if it is strictly smaller than its successor.
   *
   *    `m <= n <=> m < n + 1`
   */
  val natSubset = Lemma(in(n, N) |- subset(m, n) <=> in(m, successor(n))) {
    sorry
  }

  /**
   * Lemma --- The intersection of a natural number with the set of natural numbers is the number itself.
   *
   *    `n ∩ N = n`
   */
  val intersectionNat = Lemma(in(n, N) |- setIntersection(n, N) === n) {
    sorry
  }

  /**
   * Lemma --- If a number is smaller or equal than a natural number, then it is also a natural number.
   *
   *     `m <= n, n ∈ N |- m ∈ N`
   */
  val subsetIsNat = Lemma(subset(a, b) |- in(b, N) ==> in(a, N)) {
    sorry
  }

  /**
   * Lemma --- Induction principle for natural numbers
   *
   *     `P(0), ∀n ∈ N. P(n) => P(n + 1) |- ∀n ∈ N. P(n)`
   */
  val natInduction = Lemma((P(emptySet), forall(m, in(m, N) ==> (P(m) ==> P(successor(m))))) |- forall(n, in(n, N) ==> P(n))) {
    sorry
  }

  /**
   * Lemma --- Every number is smaller or equal than its successor.
   *
   *   `n <= n + 1`
   */
  val subsetSuccessor = Lemma(subset(n, successor(n))) {
    have(setUnion(n, singleton(n)) === union(unorderedPair(n, singleton(n))) |- subset(n, union(unorderedPair(n, singleton(n))))) by RightSubstEq.withParametersSimple(
      List((setUnion(n, singleton(n)), union(unorderedPair(n, singleton(n))))),
      lambda(s, subset(n, s))
    )(unionSubsetFirst of (a := n, b := singleton(n)))
    have(subset(n, union(unorderedPair(n, singleton(n))))) by Cut(setUnion.shortDefinition of (x := n, y := singleton(n)), lastStep)
    thenHave(successor(n) === union(unorderedPair(n, singleton(n))) |- subset(n, successor(n))) by RightSubstEq.withParametersSimple(
      List((successor(n), union(unorderedPair(n, singleton(n))))),
      lambda(s, subset(n, s))
    )
    have(thesis) by Cut(successor.shortDefinition of (x := n), lastStep)
  }

  // *************
  // * FUNCTIONS *
  // *************

  /**
   * Lemma --- Range introduction and elimination rules. If en element is in the image of a function, then it has a preimage inside its domain.
   *
   *     `functional(f) |- y ⊆ Im(f) <=> ∃x ∈ Dom(f). f(x) = y`
   */
  val functionRangeMembership = Lemma(functional(f) |- in(y, relationRange(f)) <=> ∃(x, in(x, relationDomain(f)) /\ (app(f, x) === y))) {
    sorry
  }

  /**
   * Lemma --- The restriction of a function is still a function.
   *
   *     `functional(f) |- functional(f|x)`
   */
  val functionalRestrictedFunction = Lemma(functional(f) |- functional(restrictedFunction(f, x))) {
    sorry
  }

  /**
   * Lemma --- If an element is in the image of a restricted function, then it has a preimage inside its domain.
   *
   *     `functional(f) |- y ⊆ Im(f) <=> ∃x ∈ d ∩ Dom(f). f|d(x) = y`
   */
  val restrictedFunctionRangeMembership = Lemma(functional(f) |- in(y, relationRange(restrictedFunction(f, d))) <=> ∃(x, in(x, d ∩ relationDomain(f)) /\ (app(restrictedFunction(f, d), x) === y))) {
    have(functional(f) |- in(y, relationRange(restrictedFunction(f, d))) <=> ∃(x, in(x, relationDomain(restrictedFunction(f, d))) /\ (app(restrictedFunction(f, d), x) === y))) by Cut(
      functionalRestrictedFunction of (x := d),
      functionRangeMembership of (f := restrictedFunction(f, d))
    )
    thenHave(functional(f) |- in(y, relationRange(restrictedFunction(f, d))) <=> ∃(x, in(x, d ∩ relationDomain(f)) /\ (app(restrictedFunction(f, d), x) === y))) by Substitution.ApplyRules(
      restrictedFunctionDomain of (x := d)
    )
  }

  /**
   * Lemma --- Characterization of the union of the range of a function.
   *
   *     `∪ Im(h) = {z | ∃n ∈ Dom(h). z ∈ h(n)}`
   */
  val unionRangeMembership = Lemma(functional(h) |- in(z, unionRange(h)) <=> exists(n, in(n, relationDomain(h)) /\ in(z, app(h, n)))) {
    val iffAfterAnd = have(functional(h) |- (y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y)) /\ z ∈ y) by Cut(
      functionRangeMembership of (f := h),
      rightAndEquivalence of (p1 := y ∈ relationRange(h), p2 := ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y)), p := z ∈ y)
    )
    have(functional(h) |- (y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) by Apply(equivalenceRewriting).on(
      iffAfterAnd,
      existentialConjunctionWithClosedFormula of (P := lambda(m, m ∈ relationDomain(h) /\ (app(h, m) === y)), p := z ∈ y)
    )

    thenHave(functional(h) |- ∀(y, (y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))) by RightForall

    val beforeExSwap = have(functional(h) |- ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=> ∃(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (
        P := lambda(y, y ∈ relationRange(h) /\ z ∈ y),
        Q := lambda(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))
      )
    )

    have(∃(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) <=> ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) subproof {

      have(m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y <=> m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)) by Restate
      thenHave(forall(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y <=> m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) by RightForall
      have(∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y) <=> ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (
          P := lambda(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y),
          Q := lambda(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))
        )
      )
      thenHave(forall(m, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y) <=> ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) by RightForall
      have(∃(m, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) <=> ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (
          P := lambda(y, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)),
          Q := lambda(y, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))
        )
      )
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, existentialSwap of (P2 := lambda((y, m), m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)))
    }

    val introM =
      have(functional(h) |- ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) by Apply(equivalenceRewriting).on(beforeExSwap, lastStep)

    have(
      ∀(m, (∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) <=> (m ∈ relationDomain(h) /\ z ∈ app(h, m)))
    ) by RightForall(equalityInExistentialQuantifier of (P := lambda(y, m ∈ relationDomain(h) /\ z ∈ y), y := app(h, m)))

    have(
      ∃(m, (∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) <=> ∃(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))
    ) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (
        P := lambda(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))),
        Q := lambda(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))
      )
    )

    have(functional(h) |- ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))) by Apply(equivalenceRewriting).on(
      introM,
      lastStep
    )

    have(thesis) by Apply(equivalenceRewriting).on(
      lastStep,
      unionAxiom.asInstanceOf
    )
  }

  // *************
  // * EMPTYNESS *
  // *************

  /**
   * Lemma --- The union of the empty set is the empty set.
   *
   *    `∪ ∅ = ∅`
   */
  val unionEmpty = Lemma(union(emptySet) === emptySet) {
    sorry
  }

  /**
   * Lemma --- Restricting the domain of a function to the empty set yields the empty set.
   *
   *     `h|∅ = ∅`
   */
  val restrictedFunctionEmptyDomain = Lemma(restrictedFunction(h, emptySet) === emptySet) {
    sorry
  }

  /**
   * Lemma --- If the domain of a function is non empty, then the function is non empty as well.
   *
   *     `Dom(h) != ∅ |- h != ∅`
   */
  val nonEmptyDomain = Lemma(!(relationDomain(h) === emptySet) |- !(h === emptySet)) {
    sorry
  }

  /**
   * Lemma --- A superset of a non empty set is non empty.
   *
   *     `x ⊆ y, x != ∅ |- y != ∅`
   */
  val subsetNotEmpty = Lemma((subset(x, y), !(x === emptySet)) |- !(y === emptySet)) {
    val subst = have(y === emptySet |- y === emptySet) by Hypothesis
    have((subset(x, emptySet), y === emptySet) |- (x === emptySet)) by Apply(equivalenceApply of (p1 := subset(x, emptySet))).on(emptySetIsItsOwnOnlySubset.asInstanceOf)
    thenHave((subset(x, y), y === emptySet) |- (x === emptySet)) by Substitution.ApplyRules(subst)
  }

  /**
   * Lemma --- The range of the empty relation is empty.
   * 
   *     `range(∅) = ∅`
   * 
   */
  val rangeEmpty = Lemma(relationRange(emptySet) === emptySet) {
    have(!in(pair(a, t), emptySet)) by Exact(emptySetAxiom)
    thenHave(forall(a, !in(pair(a, t), emptySet))) by RightForall
    val s0 = thenHave(!exists(a, in(pair(a, t), emptySet))) by Restate

    have(!in(t, emptySet)) by Exact(emptySetAxiom)
    have(in(t, emptySet) <=> exists(a, in(pair(a, t), emptySet))) by Tautology.from(lastStep, s0)
    val defRHS = thenHave(forall(t, in(t, emptySet) <=> exists(a, in(pair(a, t), emptySet)))) by RightForall

    have((relationRange(emptySet) === emptySet) <=> forall(t, in(t, emptySet) <=> exists(a, in(pair(a, t), emptySet)))) by InstantiateForall(emptySet)(
      relationRange.definition of (r := emptySet, z := emptySet)
    )
    have(relationRange(emptySet) === emptySet) by Tautology.from(defRHS, lastStep)
  }

  /**
   * Lemma --- The range of the empty function is empty.
   *
   *     `Im(∅) = ∅`
   */
  val unionRangeEmpty = Lemma(unionRange(emptySet) === emptySet) {
    have(unionRange(emptySet) === unionRange(emptySet)) by RightRefl
    thenHave(unionRange(emptySet) === union(emptySet)) by Substitution.ApplyRules(rangeEmpty)
    thenHave(thesis) by Substitution.ApplyRules(unionEmpty)
  }

  /**
   * Lemma --- If a function and a domain are non empty, then restricting this function to this
   * domain yields a non empty set.
   *
   *    `h != ∅, d != ∅ |- h|d != ∅`
   */
  val restrictedFunctionNotEmpty = Lemma((!(h === emptySet), !(d === emptySet)) |- !(restrictedFunction(h, d) === emptySet)) {
    sorry
  }

  // ****************
  // * MONOTONICITY *
  // ****************

  /**
   * Lemma --- Union is a monotonic operation with respect to set inclusion.
   *
   *     `x ⊆ y |- ∪ x ⊆ ∪ y`
   */
  val unionMonotonic = Lemma(subset(x, y) |- subset(union(x), union(y))) {
    sorry
  }

  /**
   * Lemma --- Range is a monotonic operation with respect to set inclusion.
   *
   *     `f ⊆ g |- Im(f) ⊆ Im(g)`
   */
  val rangeMonotonic = Lemma(subset(f, g) |- subset(relationRange(f), relationRange(g))) {
    sorry
  }

  /**
   * Lemma --- The union of the range is a monotonic operation with respect to set inclusion.
   *
   *     `f ⊆ g |- ∪ Im(f) ⊆ ∪ Im(g)`
   */
  val unionRangeMonotonic = Lemma(subset(f, g) |- subset(unionRange(f), unionRange(g))) {
    have(thesis) by Apply(unionMonotonic).on(rangeMonotonic.asInstanceOf)
  }

  /**
   * Lemma --- If two implications are true then disjuncting on both sides is also a valid implication.
   */
  val disjunctionsImplies = Lemma((p1 ==> p2, q1 ==> q2) |- (p1 \/ q1) ==> (p2 \/ q2)) {

    val right = have((p1 ==> p2, q1 ==> q2, p1) |- p2 \/ q2) by Restate
    val left = have((p1 ==> p2, q1 ==> q2, q1) |- p2 \/ q2) by Restate

    have((p1 ==> p2, q1 ==> q2, p1 \/ q1) |- p2 \/ q2) by LeftOr(left, right)
  }

  /**
   * Lemma --- If a class function F (whose representation is P) is monotonic then with respect to set inclusion, then S -> F(S) ∪ S is also
   * a monotonic function.
   *
   *      `s ⊆ t, F(s) ⊆ F(t) |- F(s) ∪ s ⊆ F(t) ∪ t`
   */
  val unionPreimageMonotonic = Lemma((subset(s, t), P(s) ==> P(t)) |- (P(s) \/ in(x, s)) ==> (P(t) \/ in(x, t))) {
    have(subset(s, t) |- forall(z, in(z, s) ==> in(z, t))) by Cut(
      subsetAxiom of (x := s, y := t),
      equivalenceApply of (p1 := subset(s, t), p2 := forall(z, in(z, s) ==> in(z, t)))
    )
    thenHave(subset(s, t) |- in(x, s) ==> in(x, t)) by InstantiateForall(x)
    have(thesis) by Cut(lastStep, disjunctionsImplies of (p1 := in(x, s), p2 := in(x, t), q1 := P(s), q2 := P(t)))
  }

  /**
   * Lemma --- Resticting a function to a smaller domain yields a subset of the original function.
   *
   *     `x ⊆ y |- f|x ⊆ f|y`
   */
  val restrictedFunctionDomainMonotonic = Lemma(subset(x, y) |- subset(restrictedFunction(f, x), restrictedFunction(f, y))) {
    sorry
  }

  // *******************
  // * SPECIFIC LEMMAS *
  // *******************

  /**
   * Lemma --- Characterization of the union of the range of a cumulative function restricted to the successor of a natural number.
   *
   *     `cumulative(h) and Dom(h) = N |- ∪ Im(h|n + 1) = h(n)`
   */
  val unionRangeCumulativeRestrictedFunction =
    Lemma((functional(h), relationDomain(h) === N, in(n, N), ∀(m, subset(m, n) ==> subset(app(h, m), app(h, n)))) |- unionRange(restrictedFunction(h, successor(n))) === app(h, n)) {

      val domainSubset = have(in(n, N) |- setIntersection(successor(n), N) === successor(n)) by Apply(intersectionNat).on(equivalenceApply of (p1 := in(n, N)), successorIsNat.asInstanceOf)

      have(functional(h) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ (successor(n) ∩ relationDomain(h)) /\ (app(restrictedFunction(h, successor(n)), m) === y)) /\ z ∈ y) by Cut(
        restrictedFunctionRangeMembership of (f := h, d := successor(n)),
        rightAndEquivalence of (p1 := y ∈ restrRange(h, successor(n)), p2 := ∃(m, m ∈ (successor(n) ∩ relationDomain(h)) /\ (app(restrictedFunction(h, successor(n)), m) === y)), p := z ∈ y)
      )

      thenHave(
        (functional(h), relationDomain(h) === N) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ (successor(n) ∩ N) /\ (app(restrictedFunction(h, successor(n)), m) === y)) /\ z ∈ y
      ) by RightSubstEq.withParametersSimple(
        List((relationDomain(h), N)),
        lambda(s, (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ (successor(n) ∩ s) /\ (app(restrictedFunction(h, successor(n)), m) === y)) /\ z ∈ y)
      )

      thenHave(
        (functional(h), in(n, N), relationDomain(h) === N, successor(n) ∩ N === successor(n)) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ (successor(n) ∩ N) /\ (app(restrictedFunction(h, successor(n)), m) === y)
        ) /\ z ∈ y
      ) by Weakening

      thenHave(
        (functional(h), in(n, N), relationDomain(h) === N, successor(n) ∩ N === successor(n)) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(
          m,
          m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)), m) === y)
        ) /\ z ∈ y
      ) by RightSubstEq.withParametersSimple(
        List((successor(n) ∩ N, successor(n))),
        lambda(s, (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ s /\ (app(restrictedFunction(h, successor(n)), m) === y)) /\ z ∈ y)
      )

      have(
        (functional(h), in(n, N), relationDomain(h) === N) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)), m) === y)) /\ z ∈ y
      ) by Cut(domainSubset, lastStep)

      have(
        (functional(h), in(n, N), relationDomain(h) === N) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)), m) === y) /\ z ∈ y)
      ) by Apply(equivalenceRewriting).on(
        lastStep,
        existentialConjunctionWithClosedFormula of (P := lambda(m, m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)), m) === y)), p := z ∈ y)
      )

      thenHave(
        (functional(h), in(n, N), relationDomain(h) === N) |- ∀(
          y,
          (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)), m) === y) /\ z ∈ y)
        )
      ) by RightForall

      have(
        (functional(h), in(n, N), relationDomain(h) === N) |- ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(
          y,
          ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)), m) === y) /\ z ∈ y)
        )
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (
          P := lambda(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y),
          Q := lambda(y, ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(h, successor(n)), m) === y) /\ z ∈ y))
        )
      )

      val introM =
        thenHave(
          (functional(h), in(n, N), relationDomain(h) === N) |- ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(
            m,
            ∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))
          )
        ) by Tableau

      have((∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(restrictedFunction(h, successor(n)), m))) by Exact(
        equalityInExistentialQuantifier of (P := lambda(y, m ∈ successor(n) /\ z ∈ y))
      )

      thenHave(m ∈ successor(n) |- (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(h, m))) by Substitution.ApplyRules(
        restrictedFunctionApplication
      )
      thenHave((∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(h, m))) by Tableau

      thenHave(subset(m, n) <=> m ∈ successor(n) |- (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))) <=> (subset(m, n) /\ z ∈ app(h, m))) by RightSubstIff
        .withParametersSimple(
          List((m ∈ successor(n), subset(m, n))),
          lambda(p, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))) <=> (p /\ z ∈ app(h, m)))
        )

      have(in(n, N) |- (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))) <=> (subset(m, n) /\ z ∈ app(h, m))) by Cut(natSubset, lastStep)

      thenHave(
        in(n, N) |- ∀(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))) <=> (subset(m, n) /\ z ∈ app(h, m)))
      ) by RightForall

      have(
        in(n, N) |- ∃(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y)))) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))
      ) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (
          P := lambda(m, ∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(h, successor(n)), m) === y))),
          Q := lambda(m, subset(m, n) /\ z ∈ app(h, m))
        )
      )

      have((functional(h), in(n, N), relationDomain(h) === N) |- ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Apply(equivalenceRewriting).on(
        introM,
        lastStep
      )

      val unionIsExists =
        have((functional(h), in(n, N), relationDomain(h) === N) |- z ∈ unionRange(restrictedFunction(h, successor(n))) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Apply(equivalenceRewriting).on(
          lastStep,
          unionAxiom.asInstanceOf
        )

      val cumulativeAssumption = ∀(m, subset(m, n) ==> subset(app(h, m), app(h, n)))

      have(cumulativeAssumption |- ∃(m, subset(m, n) /\ z ∈ app(h, m)) <=> z ∈ app(h, n)) subproof {
        val seq1 = have(z ∈ app(h, n) |- z ∈ app(h, n)) by Hypothesis
        have(z ∈ app(h, n) |- subset(n, n) /\ z ∈ app(h, n)) by RightAnd(seq1, subsetReflexivity of (x := n))
        thenHave(z ∈ app(h, n) |- ∃(m, subset(m, n) /\ z ∈ app(h, m))) by RightExists
        val backward = thenHave(cumulativeAssumption |- z ∈ app(h, n) ==> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Weakening

        have(cumulativeAssumption |- cumulativeAssumption) by Hypothesis
        thenHave(cumulativeAssumption |- subset(m, n) ==> subset(app(h, m), app(h, n))) by InstantiateForall(m)
        have((cumulativeAssumption, subset(m, n), z ∈ app(h, m)) |- forall(z, z ∈ app(h, m) ==> z ∈ app(h, n))) by Apply(equivalenceApply).on(
          lastStep,
          subsetAxiom
        )
        thenHave((cumulativeAssumption, subset(m, n) /\ z ∈ app(h, m)) |- z ∈ app(h, n)) by InstantiateForall(z)
        thenHave((cumulativeAssumption, ∃(m, subset(m, n) /\ z ∈ app(h, m))) |- z ∈ app(h, n)) by LeftExists
        val forward = thenHave(cumulativeAssumption |- ∃(m, subset(m, n) /\ z ∈ app(h, m)) ==> z ∈ app(h, n)) by RightImplies

        have(thesis) by RightIff(forward, backward)
      }

      have((functional(h), in(n, N), relationDomain(h) === N, cumulativeAssumption) |- (z ∈ unionRange(restrictedFunction(h, successor(n)))) <=> z ∈ app(h, n)) by Apply(equivalenceRewriting).on(
        unionIsExists,
        lastStep
      )
      thenHave((functional(h), in(n, N), relationDomain(h) === N, cumulativeAssumption) |- ∀(z, z ∈ unionRange(restrictedFunction(h, successor(n))) <=> z ∈ app(h, n))) by RightForall

      have(thesis) by Apply(equivalenceApply).on(lastStep, extensionalityAxiom.asInstanceOf)
    }

}