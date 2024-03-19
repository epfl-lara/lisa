import lisa.SetTheoryLibrary
import lisa.maths.settheory.SetTheory
import lisa.maths.settheory.SetTheory.*
//import lisa.maths.settheory.InductiveSets.*
import lisa.maths.settheory.Comprehensions.*
import lisa.maths.settheory.orderings.Ordinals.*
import lisa.maths.settheory.orderings.Recursion.*
import lisa.maths.Quantifiers.*


import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.OutputManager
import lisa.prooflib.Library

import lisa.kernel.proof.SequentCalculus.*
import java.time.Instant
import scala.collection.immutable.HashMap
import lisa.utils.parsing.UnreachableException
import lisa.maths.settheory.types.TypeLib.{any, |=>, given}
import lisa.maths.settheory.types.TypeSystem.{*, given}

object ADTExternalTheorems extends lisa.Main {
  val pair = ConstantFunctionLabel("pair", 2)
  addSymbol(pair)

  val a = variable
  val b = variable
  val c = variable
  val d = variable

  val f = variable
  val g = variable

  val n = variable
  val m = variable

  val p = formulaVariable
  val p1 = formulaVariable
  val p2 = formulaVariable
  val p3 = formulaVariable

  val x = variable
  val y = variable

  val P = predicate[1]
  val P2 = predicate[2]

  val substitutionThm = Lemma((x === y, P(x)) |- P(y)) {
    val s0 = have(x === y |- x === y) by Restate
    have(P(x) |- P(x)) by Hypothesis
    thenHave(thesis) by Substitution.ApplyRules(s0)
  }

  val equivalenceRewriting = Lemma((p1 <=> p2, p2 <=> p3) |- p1 <=> p3) {
    have(thesis) by Tautology
  }

  val equivalenceReflexivity = Lemma(p1 <=> p1) {
    have(thesis) by Tautology
  }

  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2) {
    have(thesis) by Tautology
  }

  val permExists = Lemma(exists(x, exists(y, P2(x, y))) <=> exists(y, exists(x, P2(x, y)))) {
    have(thesis) by Tableau
  }

  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2) {
    have(thesis) by Tautology
  }

  val negEquivalence = Lemma(p1 <=> p2 |- !p1 <=> !p2) {
    have(thesis) by Tautology
  }

  val restrictedFunctionRangeMembership = Lemma(functional(g) |- in(y, relationRange(restrictedFunction(f, d))) <=> ∃(m, in(m, d) /\ (app(restrictedFunction(f, d), m) === y))) {
    sorry
  }

  val rangeMonotonic = Lemma(subset(f, g) |- subset(relationRange(f), relationRange(g))) {
    sorry
  }

  val restrictedFunctionDomainMonotonic = Lemma(subset(m, n) |- subset(restrictedFunction(f, m), restrictedFunction(f, n))) {
    sorry
  }

  val functionRangeMembership = Lemma(functional(g) |- in(y, relationRange(f)) <=> ∃(m, in(m, relationDomain(f)) /\ (app(f, m) === y))) {
    sorry
  }

  val rightAndEquivalence = Lemma(p1 <=> p2 |- (p1 /\ p) <=> (p2 /\ p)) {
    have(thesis) by Tableau
  }

  val notInSelf = Lemma(in(x, x) |- ()) {
    sorry
  }

  val elementOrEmpty = Lemma(exists(y, in(y, x)) \/ (x === emptySet)) {
    sorry
  }

  val unionMonotic = Lemma(subset(x, y) |- subset(union(x), union(y))) {
    sorry
  }

  val subsetNotEmpty = Lemma((subset(x, y), !(x === emptySet)) |- !(y === emptySet)) {
    sorry
  }

  val restrictedFunctionNotEmpty = Lemma((!(g === emptySet), !(n === emptySet)) |- !(restrictedFunction(g, n) === emptySet)) {
    sorry
  }

  val emptyFunction = Lemma(!(relationDomain(g) === emptySet) |- !(g === emptySet)) {
    sorry
  }

  val pairExtensionality = Lemma((pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))) {
    sorry
  }


  // natural numbers
  val N = Constant("N")
  addSymbol(N)

  // Axiom: N is an ordinal
  val naturalOrdinal = Axiom(ordinal(N))

  // Axiom: 0 ∈ N
  val zeroIsNat = Lemma(in(emptySet, N)) {
    sorry
  }

  val natNotEmpty = Lemma(!(N === emptySet)) {
    sorry
  }

  val zeroInNat = Lemma(in(n, N) |- in(emptySet, n) \/ (n === emptySet)) {
    sorry
  }

  val successorHomorphic = Lemma((in(n, N)) |- in(m, n) <=> in(successor(m), successor(n))) {
    sorry
  }

  val successorInjectivity = Lemma((n === m) <=> (successor(n) === successor(m))) {
    sorry
  }

  // Axiom: 0 ∈ N
  val zeroIsInSuccessor = Lemma(in(n, N) |- in(emptySet, successor(n))) {
    sorry
  }

  // Axiom: if n ∈ N then successor(n) ∈ N
  val successorIsNat = Lemma(in(n, N) <=> in(successor(n), N)) {
    sorry
  }

  val natWeakTransitive = Lemma((in(a, b), in(b, N)) |- in(a, N)) {
    sorry
  }

  // Axiom: Successor is not empty
  val successorNotEmpty = Lemma(in(n, N) |- exists(m, in(m, successor(n)))) {
    sorry
  }

  val natTransitive = Lemma((in(a, b), in(b, c), in(c, N)) |- in(a, c)) {
    sorry
  }

  val natTotalOrder = Lemma((in(a, N), in(b, N)) |- in(a, successor(b)) \/ in(b, a)) {
    sorry
  }

  val zeroIsNotSucc = Lemma(!(successor(n) === emptySet)) {
    sorry
  }

  val natSubset = Lemma(in(b, N) |- subset(a, b) <=> in(a, successor(b))) {
    sorry
  }

  val subsetIsNat = Lemma(subset(a, b) |- in(b, N) ==> in(a, N)) {
    sorry
  }

  val natInduction = Lemma(P(emptySet) ==> (forall(m, in(m, N) ==> (P(m) ==> P(successor(m)))) ==> forall(n, in(n, N) ==> P(n)))) {
    sorry
  }

  // Axiom: Successor is not empty
  val inSuccessor = Axiom(in(n, successor(n)))

  val unionEmpty = Lemma(union(emptySet) === emptySet) {
    sorry
  }

  val restrictedFunctionEmptyDomain = Lemma(restrictedFunction(f, emptySet) === emptySet) {
    sorry
  }

  def toTerm(n: Int): Term = 
    if n == 0 then
      emptySet
    else 
      successor(toTerm(n - 1))

}

object ADTTactic{

  import ADTExternalTheorems.*

  /**
    * Variable imports
    */
  val k = variable
  val r = variable
  val s = variable
  val t = variable

  val z = variable
  val Q = predicate[1]

  val schemPred = predicate[1]


  def \/(s: Iterable[Formula]) = 
    if s.isEmpty then False 
    else s.fold(False)(_ \/ _)
  def /\(s: Iterable[Formula]) = 
    if s.isEmpty then True
    else s.fold(True)(_ /\ _)

  def removeConstants(f: Formula): Formula =
    f match
      case Or(False, phi) => removeConstants(phi)
      case Or(phi, False) => removeConstants(phi)
      case Or(phi, psi) => removeConstants(phi) \/ removeConstants(psi)
      case And(True, phi) => removeConstants(phi)
      case And(phi, True) => removeConstants(phi)
      case And(phi, psi) => removeConstants(phi) /\ removeConstants(psi)
      case Implies(True, phi) => removeConstants(phi)
      case Implies(phi, psi) => Implies(removeConstants(phi), removeConstants(psi))
      case _ => f
    

  sealed trait Type
  case object Self extends Type
  case class BaseType(t: Term) extends Type

  type Tag = String
  var tagCounter = 0

  /**
   * One of the constructors of an algebraic data type.
   *
   * @tparam N arity of the constructor, i.e. the number of arguments it takes
   * @param adt name of the ADT
   * @param name name of the constructor
   * @param typeArgs types of the parameters of the constructor
   */
  class Constructor(using line: sourcecode.Line, file: sourcecode.File)(val name: String, val typeArgs: Seq[Type]) {

    val tag: Int = tagCounter
    tagCounter = tagCounter + 1

    val tagTerm: Term = toTerm(tag)

    /**
     * Number of arguments in this constructor
     */
    val arity: Int = typeArgs.length

    /**
     * List of variables used in the definition of this constructor
     */
    val variables: Seq[Variable] = for i <- 0 until arity yield Variable(s"a${i}")

    val typeVariables: Seq[Variable] = 
      def termTypeVars(appliedTerm: Term): Seq[Variable] = 
        appliedTerm match
          case v: Variable => Seq(v)
          case _: Constant => Seq.empty
          case af : AppliedFunctional => af.args.flatMap(termTypeVars)
        
      typeArgs.flatMap({
        case Self => Seq.empty
        case BaseType(te) => termTypeVars(te)
      }).distinct

              
    /**
     * Internally, an instance of this constructor is represented as a list.
     * The first element of this list is the complete name of this constructor
     * and the following elements are its arguments. We represent lists as chained
     * pairs followed by the empty set.
     *
     * e.g. Cons(1, Cons(2, Nil)) --> (1, (2, ∅))
     *
     * @param args the arguments of this instance of the constructor
     */
    def appliedTerm(targs: Seq[Term], args: Seq[Term]): Term = pair(tagTerm, subterm(targs, args))

    def appliedTerm(args: Seq[Term]): Term = appliedTerm(typeVariables, args)

    val appliedTerm: Term = appliedTerm(variables)

    /**
     * @see [[this.appliedTerm]]
     */
    def subterm(targs: Seq[Term], args: Seq[Term]): Term = args.foldRight(emptySet)((t, acc: Term) => pair(t.substitute(typeVariables.zip(targs).map(_ := _): _*), acc))

    def subterm(args: Seq[Term]): Term = subterm(typeVariables, args)

    def subterm: Term = subterm(variables)

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
     *
     * e.g. Cons(head1, tail1) === Cons(head2, tail2) <=> head1 === head1
     */
    val injectivityThm =

      // variable sequences x_0, ..., x_n-1 and y_0, ..., y_n-1
      val xs = for i <- 0 until arity yield Variable(s"x${i}")
      val ys = for i <- 0 until arity yield Variable(s"y${i}")

      // internal representation of this constructor instantiated with xs ys
      val txs = appliedTerm(xs)
      val tys = appliedTerm(ys)

      if arity == 0 then 
        Theorem(txs === tys) {
          have(thesis) by Restate
        }
      else
        // follows from pair injectivity
        Theorem((txs === tys) <=> /\ (xs.zip(ys).map(_ === _))) {
        

          have((txs === tys) <=> ((tagTerm === tagTerm) /\ (subterm(xs) === subterm(ys)))) by Exact(pairExtensionality)
          thenHave((txs === tys) <=> (subterm(xs) === subterm(ys))) by Tautology

          // list of the possible cuts of xs and ys without the first one (empty list, full list)
          val cumulX = xs.scanLeft[(List[Variable], List[Variable])]((Nil, xs.toList))((acc, _) => (acc._2.head :: acc._1, acc._2.tail)).tail
          val cumulY = xs.scanLeft[(List[Variable], List[Variable])]((Nil, ys.toList))((acc, _) => (acc._2.head :: acc._1, acc._2.tail)).tail

          for pl <- cumulX.zip(cumulY) do
            val left = /\ (pl._1._1.zip(pl._2._1).map(_ === _))
            val rightX = subterm(pl._1._2)
            val rightY = subterm(pl._2._2)
            have((txs === tys) <=> left /\ (rightX === rightY)) by Tautology.from(lastStep, pairExtensionality of (a := pl._1._1.head, b := rightX, c := pl._2._1.head, d := rightY))
        }

  }



  // Helper: compute the union of the range of a functional
  def unionRange(f: Term) = union(relationRange(f))
  def restrRange(f: Term, n: Term) = relationRange(restrictedFunction(f, n))


  val unionRangeMonotonic = Lemma(subset(f, g) |- subset(unionRange(f), unionRange(g))) {
    have(thesis) by Apply(unionMonotic).on(rangeMonotonic.asInstanceOf)
  }


  val unionRangeEmpty = Lemma(unionRange(emptySet) === emptySet) {
    have(!in(SetTheory.pair(a, t), emptySet)) by Exact(emptySetAxiom)
    thenHave(forall(a, !in(SetTheory.pair(a, t), emptySet))) by RightForall
    val s0 = thenHave(!exists(a, in(SetTheory.pair(a, t), emptySet))) by Restate

    have(!in(t, emptySet)) by Exact(emptySetAxiom)
    have(in(t, emptySet) <=> exists(a, in(SetTheory.pair(a, t), emptySet))) by Tautology.from(lastStep, s0)
    val defRHS = thenHave(forall(t, in(t, emptySet) <=> exists(a, in(SetTheory.pair(a, t), emptySet)))) by RightForall

    have((relationRange(emptySet) === emptySet) <=> forall(t, in(t, emptySet) <=> exists(a, in(SetTheory.pair(a, t), emptySet)))) by InstantiateForall(emptySet)(
      relationRange.definition of (r := emptySet, z := emptySet)
    )
    have(relationRange(emptySet) === emptySet) by Apply(equivalenceRevApply).on(defRHS, lastStep)

    have(unionRange(emptySet) === union(emptySet)) by Substitution.ApplyRules(lastStep)(have(unionRange(emptySet) === unionRange(emptySet)) by Restate)
    thenHave(thesis) by Substitution.ApplyRules(unionEmpty)
  }

  val unionRangeMembership = Lemma(functional(g) |- in(z, unionRange(g)) <=> exists(n, in(n, relationDomain(g)) /\ in(z, app(g, n)))) {
    val iffAfterAnd = have(functional(g) |- (y ∈ relationRange(g) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(g) /\ (app(g, m) === y)) /\ z ∈ y) by Apply(
      rightAndEquivalence
    ).on(Seq(have(functionRangeMembership)), excluding = Seq(g))

    have(functional(g) |- (y ∈ relationRange(g) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y)) by Apply(equivalenceRewriting).on(
      iffAfterAnd,
      existentialConjunctionWithClosedFormula of (P := lambda(m, m ∈ relationDomain(g) /\ (app(g, m) === y)), p := z ∈ y)
    )

    thenHave(functional(g) |- ∀(y, (y ∈ relationRange(g) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y))) by RightForall

    val beforeExSwap = have(functional(g) |- ∃(y, y ∈ relationRange(g) /\ z ∈ y) <=> ∃(y, ∃(m, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y))) by Apply(
      existentialEquivalenceDistribution of (
        P := lambda(y, y ∈ relationRange(g) /\ z ∈ y),
        Q := lambda(y, ∃(m, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y))
      )
    ).on(lastStep)

    have(∃(y, ∃(m, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y)) <=> ∃(m, ∃(y, m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y)))) subproof {
      val exSwap = have(∃(y, ∃(m, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y)) <=> ∃(m, ∃(y, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y))) by Exact(
        permExists of (P2 := lambda((y, m), m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y))
      )
      have(m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y <=> m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y)) by Tautology
      thenHave(∃(m, ∃(y, m ∈ relationDomain(g) /\ (app(g, m) === y) /\ z ∈ y)) <=> ∃(m, ∃(y, m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y)))) by Tableau
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, exSwap)
    }

    val introM =
      have(functional(g) |- ∃(y, y ∈ relationRange(g) /\ z ∈ y) <=> ∃(m, ∃(y, m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y)))) by Apply(equivalenceRewriting).on(beforeExSwap, lastStep)

    have((∃(y, m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y))) <=> (m ∈ relationDomain(g) /\ z ∈ app(g, m))) by Exact(
      equalityInExistentialQuantifier of (P := lambda(y, m ∈ relationDomain(g) /\ z ∈ y))
    )
    thenHave(
      ∀(m, (∃(y, m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y))) <=> (m ∈ relationDomain(g) /\ z ∈ app(g, m)))
    ) by RightForall

    have(
      ∃(m, (∃(y, m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y)))) <=> ∃(m, m ∈ relationDomain(g) /\ z ∈ app(g, m))
    ) by Apply(
      existentialEquivalenceDistribution of (
        P := lambda(m, ∃(y, m ∈ relationDomain(g) /\ z ∈ y /\ (app(g, m) === y))),
        Q := lambda(m, m ∈ relationDomain(g) /\ z ∈ app(g, m))
      )
    ).on(lastStep)

    have(functional(g) |- ∃(y, y ∈ relationRange(g) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(g) /\ z ∈ app(g, m))) by Apply(equivalenceRewriting).on(
      introM,
      lastStep
    )

    val unionIsExists = have(functional(g) |- z ∈ unionRange(g) <=> ∃(m, m ∈ relationDomain(g) /\ z ∈ app(g, m))) by Apply(equivalenceRewriting).on(
      Seq(
        lastStep,
        have(unionAxiom)
      )
    )
  }

  lazy val unionRangeLemma = Lemma((functional(g), ∀(m, in(m, successor(n)) ==> subset(app(g, m), app(g, n)))) |- unionRange(restrictedFunction(g, successor(n))) === app(g, n)) {

    val iffAfterAnd = have(functional(g) |- (y ∈ restrRange(g, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(g, successor(n)), m) === y)) /\ z ∈ y) by Apply(
      rightAndEquivalence
    ).on(restrictedFunctionRangeMembership.asInstanceOf)

    have(functional(g) |- (y ∈ restrRange(g, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(g, successor(n)), m) === y) /\ z ∈ y)) by Apply(equivalenceRewriting).on(
      iffAfterAnd,
      existentialConjunctionWithClosedFormula of (P := lambda(m, m ∈ successor(n) /\ (app(restrictedFunction(g, successor(n)), m) === y)), p := z ∈ y)
    )

    thenHave(functional(g) |- ∀(y, (y ∈ restrRange(g, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(g, successor(n)), m) === y) /\ z ∈ y))) by RightForall

    have(functional(g) |- ∃(y, y ∈ restrRange(g, successor(n)) /\ z ∈ y) <=> ∃(y, ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(g, successor(n)), m) === y) /\ z ∈ y))) by Apply(
      existentialEquivalenceDistribution of (
        P := lambda(y, y ∈ restrRange(g, successor(n)) /\ z ∈ y),
        Q := lambda(y, ∃(m, m ∈ successor(n) /\ (app(restrictedFunction(g, successor(n)), m) === y) /\ z ∈ y))
      )
    ).on(lastStep)

    val introM =
      thenHave(functional(g) |- ∃(y, y ∈ restrRange(g, successor(n)) /\ z ∈ y) <=> ∃(m, ∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(g, successor(n)), m) === y)))) by Tableau

    have((∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(g, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(restrictedFunction(g, successor(n)), m))) by Exact(
      equalityInExistentialQuantifier of (P := lambda(y, m ∈ successor(n) /\ z ∈ y))
    )

    thenHave(m ∈ successor(n) |- (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(g, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(g, m))) by Substitution.ApplyRules(
      restrictedFunctionApplication
    )
    thenHave((∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(g, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(g, m))) by Tableau

    thenHave(
      ∀(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(g, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(g, m)))
    ) by RightForall

    have(
      ∃(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(g, successor(n)), m) === y)))) <=> ∃(m, m ∈ successor(n) /\ z ∈ app(g, m))
    ) by Apply(
      existentialEquivalenceDistribution of (
        P := lambda(m, ∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(restrictedFunction(g, successor(n)), m) === y))),
        Q := lambda(m, m ∈ successor(n) /\ z ∈ app(g, m))
      )
    ).on(lastStep)

    have(functional(g) |- ∃(y, y ∈ restrRange(g, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ successor(n) /\ z ∈ app(g, m))) by Apply(equivalenceRewriting).on(
      introM,
      lastStep
    )

    val unionIsExists = have(functional(g) |- z ∈ unionRange(restrictedFunction(g, successor(n))) <=> ∃(m, m ∈ successor(n) /\ z ∈ app(g, m))) by Apply(equivalenceRewriting).on(
      Seq(
        lastStep,
        have(unionAxiom)
      )
    )

    have(∀(m, in(m, successor(n)) ==> subset(app(g, m), app(g, n))) |- ∃(m, m ∈ successor(n) /\ z ∈ app(g, m)) <=> z ∈ app(g, n)) subproof {
      val seq1 = have(z ∈ app(g, n) |- z ∈ app(g, n)) by Hypothesis
      val seq2 = have(z ∈ app(g, n) |- n ∈ successor(n)) by Exact(inSuccessor)
      have(z ∈ app(g, n) |- n ∈ successor(n) /\ z ∈ app(g, n)) by RightAnd(seq1, seq2)
      val ccl1 = thenHave(z ∈ app(g, n) |- ∃(m, m ∈ successor(n) /\ z ∈ app(g, m))) by RightExists

      have(∀(a, a ∈ successor(n) ==> subset(app(g, a), app(g, n))) |- ∀(a, a ∈ successor(n) ==> subset(app(g, a), app(g, n)))) by Hypothesis
      thenHave(∀(a, a ∈ successor(n) ==> subset(app(g, a), app(g, n))) |- m ∈ successor(n) ==> subset(app(g, m), app(g, n))) by InstantiateForall(m)
      have((∀(a, a ∈ successor(n) ==> subset(app(g, a), app(g, n))), m ∈ successor(n), z ∈ app(g, m)) |- forall(z, z ∈ app(g, m) ==> z ∈ app(g, n))) by Apply(equivalenceApply).on(
        lastStep,
        subsetAxiom
      )
      thenHave((∀(a, a ∈ successor(n) ==> subset(app(g, a), app(g, n))), m ∈ successor(n) /\ z ∈ app(g, m)) |- z ∈ app(g, n)) by InstantiateForall(z)
      val ccl2 = thenHave((∀(a, a ∈ successor(n) ==> subset(app(g, a), app(g, n))), ∃(m, m ∈ successor(n) /\ z ∈ app(g, m))) |- z ∈ app(g, n)) by LeftExists

      have(thesis) by Tautology.from(ccl1, ccl2)
    }

    have((functional(g), ∀(m, in(m, successor(n)) ==> subset(app(g, m), app(g, n)))) |- (z ∈ unionRange(restrictedFunction(g, successor(n)))) <=> z ∈ app(g, n)) by Apply(equivalenceRewriting).on(
      unionIsExists,
      lastStep
    )
    thenHave((functional(g), ∀(m, in(m, successor(n)) ==> subset(app(g, m), app(g, n)))) |- ∀(z, z ∈ unionRange(restrictedFunction(g, successor(n))) <=> z ∈ app(g, n))) by RightForall
    have(thesis) by Apply(equivalenceApply).on(lastStep, extensionalityAxiom.asInstanceOf)
  }

  class UntypedADT(using line: sourcecode.Line, file: sourcecode.File)(val name: String, val constructors: Seq[Constructor]) {

    println(s"Generating $name...")

    val before =  System.nanoTime

    val typeVariables = constructors.flatMap(_.typeVariables).distinct

    val constructorMap: Map[String, Constructor] = constructors.map(c => (c.name -> c)).toMap

    val exVar: Map[Constructor, Seq[Variable]] = constructors.map(c => (c -> (for i <- 0 until c.arity yield Variable(s"x${i}")))).toMap

    def consVarMembership(c: Constructor, vars: Seq[Term], s: Term): Formula = /\ (vars.zip(c.typeArgs).map((v, t) => in(v, getTermOrElse(t, s))))
    def consVarMembership(c: Constructor, s: Term): Formula = consVarMembership(c, c.variables, s)
    def consExVarMembership(c: Constructor, s: Term): Formula = consVarMembership(c, exVar(c), s)

    def isConstructor(c: Constructor, x: Term, s: Term): Formula = exVar(c).foldRight(consVarMembership(c, exVar(c), s) /\ (x === c.appliedTerm(exVar(c))))((exv, f) => exists(exv, f))
    def isConstructor(x: Term, s: Term): Formula = \/ (constructors.map(c => isConstructor(c, x, s)))


    def getTermOrElse(t: Type, s: Term) = 
      t match {
        case Self => s
        case BaseType(te) => te
      } 


    def inInductiveFun(s: Term)(x: Term) = isConstructor(x, s) \/ in(x, s)

    val inductiveFunMonotonic = Lemma(subset(s, t) |- inInductiveFun(s)(x) ==> inInductiveFun(t)(x)) {

      val subsetST = subset(s, t)

      have(subsetST |- forall(z, in(z, s) ==> in(z, t))) by Apply(equivalenceApply of (p1 := subsetST)).on(subsetAxiom.asInstanceOf)
      val subs = thenHave(subsetST |- in(z, s) ==> in(z, t)) by InstantiateForall(z)

      val subsetSeq = 
        for c <- constructors yield
          val labelWithExVar = c.appliedTerm(exVar(c))
          val labelEq = labelWithExVar === x

          val consExVarMembershipS = consExVarMembership(c, s)
          val consExVarMembershipSAndEq = consExVarMembershipS /\ labelEq
          val consExVarMembershipT = consExVarMembership(c, t)
          val consExVarMembershipTAndEq = consExVarMembershipT /\ labelEq

          val andSeq = for ((v, ty) <- exVar(c).zip(c.typeArgs)) yield {
            ty match
              case Self => have((subset(s, t), consExVarMembershipSAndEq) |- in(v, t)) by Weakening(subs of (z := v))
              case BaseType(te) => have((subset(s, t), consExVarMembershipSAndEq) |- in(v, te)) by Restate
          }

          val s0l = have((subset(s, t), consExVarMembershipSAndEq) |- consExVarMembershipT) by AndAggregate(andSeq)
          val s0r = have((subset(s, t), consExVarMembershipSAndEq) |- labelEq) by Restate

          have((subset(s, t), consExVarMembershipSAndEq) |- consExVarMembershipTAndEq) by RightAnd(s0l, s0r)

          // (subsetST, consExVarMembershipSAndEq) |- isConstructor(x, t)
          exVar(c).foldRight(lastStep) ( (v, acc) => 
            thenHave((subsetST, consExVarMembershipSAndEq) |- exists(v, acc.statement.right.head)) by RightExists
          )
          
          // (subsetST, isConstructor(x, s)) |- isConstructor(x, t)
          (exVar(c).foldRight((lastStep, consExVarMembershipSAndEq)) ( (v, acc) => 
            val (accFact, accSeq) = acc
            (thenHave((subsetST, exists(v, accSeq)) |- isConstructor(c, x, t)) by LeftExists, exists(v, accSeq))
          ))._1

      have((subsetST, isConstructor(x, s)) |- isConstructor(x, t)) by Tautology.from(subsetSeq: _*)
      have(thesis) by Tautology.from(lastStep, subs of (z := x))

    }

    val constructorInInductiveFun = constructorMap.map((k, c) => k -> Lemma(consVarMembership(c, s) |- inInductiveFun(s)(c.appliedTerm)) {

        val andl = have(consVarMembership(c, s) |- consVarMembership(c, s)) by Hypothesis
        val andr = have(c.appliedTerm === c.appliedTerm) by Restate
        have(consVarMembership(c, s) |- consVarMembership(c, s) /\ (c.appliedTerm === c.appliedTerm)) by RightAnd(andl, andr)

        ((c.variables.zip(exVar(c))).foldRight((lastStep, c.variables, List[Variable]()))) ( (el, acc) => 

          val (va, v) = el
          val (_, accVa, accVb) = acc

          val varsLeft = accVa.init
          val varsRight = v :: accVb

          val vars = varsLeft ++ varsRight
          val rightSeq = accVb.foldRight(consVarMembership(c, vars, s) /\ (c.appliedTerm(vars) === c.appliedTerm))((exV, f) =>
            exists(exV, f)
          )

          (thenHave(consVarMembership(c, s) |- exists(v, rightSeq)) by RightExists, varsLeft, varsRight)
        )._1

        thenHave(consVarMembership(c, s) |- inInductiveFun(s)(c.appliedTerm)) by Tautology
    })


    def inTransRecFun(f: Term)(x: Term) = !(f === emptySet) /\ inInductiveFun(unionRange(f))(x)

    val transRecFunMonotonic = Lemma(subset(f, g) |- inTransRecFun(f)(x) ==> inTransRecFun(g)(x)) {
      val s0l = have(subset(f, g) |- subset(unionRange(f), unionRange(g))) by Restate.from(unionRangeMonotonic)
      val s0r = have(subset(unionRange(f), unionRange(g)) |- inInductiveFun(unionRange(f))(x) ==> inInductiveFun(unionRange(g))(x)) by Restate.from(inductiveFunMonotonic of (s := unionRange(f), t := unionRange(g)))
      have(subset(f, g) |- inInductiveFun(unionRange(f))(x) ==> inInductiveFun(unionRange(g))(x)) by Cut(s0l, s0r)
      val s1r = thenHave((subset(f, g), inTransRecFun(f)(x)) |- inInductiveFun(unionRange(g))(x)) by Weakening

      val s1l = have((subset(f, g), inTransRecFun(f)(x)) |- !(g === emptySet)) by Weakening(subsetNotEmpty of (x := f, y := g))
      have((subset(f, g), inTransRecFun(f)(x)) |- inTransRecFun(g)(x)) by RightAnd(s1l, s1r)
    }

    def isHeightFun(g: Term) = functional(g) /\ (relationDomain(g) === N) /\ forall(b, in(b, N) ==> forall(x, in(x, app(g, b)) <=> inTransRecFun(restrictedFunction(g, b))(x)))

    val heightFunNonEmpty = Lemma(isHeightFun(g) |- !(g === emptySet)) {
      val subst = have(isHeightFun(g) |- relationDomain(g) === N) by Restate
      have((isHeightFun(g), relationDomain(g) === emptySet, N === emptySet) |- ()) by Weakening(natNotEmpty)
      thenHave((isHeightFun(g), relationDomain(g) === emptySet, emptySet === emptySet) |- ()) by Substitution.ApplyRules(subst)
      thenHave(isHeightFun(g) |- !(relationDomain(g) === emptySet)) by Restate
      have(isHeightFun(g) |- !(g === emptySet)) by Apply(emptyFunction).on(lastStep)
    }

    val hasHeightBelow = Lemma((isHeightFun(g), in(n, N)) |- in(x, app(g, n)) <=> inTransRecFun(restrictedFunction(g, n))(x)) {
      have(
        forall(b, in(b, N) ==> forall(x, in(x, app(g, b)) <=> inTransRecFun(restrictedFunction(g, b))(x))) |- forall(b, in(b, N) ==> forall(x, in(x, app(g, b)) <=> inTransRecFun(restrictedFunction(g, b))(x)))
      ) by Hypothesis
      thenHave(isHeightFun(g) |- in(n, N) ==> forall(x, in(x, app(g, n)) <=> inTransRecFun(restrictedFunction(g, n))(x))) by InstantiateForall(n)
      thenHave((isHeightFun(g), in(n, N)) |- forall(x, in(x, app(g, n)) <=> inTransRecFun(restrictedFunction(g, n))(x))) by Restate
      thenHave((isHeightFun(g), in(n, N)) |- in(x, app(g, n)) <=> inTransRecFun(restrictedFunction(g, n))(x)) by InstantiateForall(x)
    }

    val heightFunCumulative = Lemma((isHeightFun(g), in(n, N)) |- ∀(m, in(m, successor(n)) ==> subset(app(g, m), app(g, n)))) {
      have((isHeightFun(g), in(n, N)) |- subset(m, n) <=> in(m, successor(n))) by Exact(natSubset)
      thenHave((isHeightFun(g), in(n, N)) |- in(m, successor(n)) <=> subset(m, n)) by Restate
      val imp0 = have((isHeightFun(g), in(n, N)) |- in(m, successor(n)) ==> subset(m, n)) by Apply(equivalenceApply).on(lastStep)

      have((isHeightFun(g), in(n, N), subset(m, n)) |- in(x, app(g, m)) <=> inTransRecFun(restrictedFunction(g, m))(x)) by Apply(hasHeightBelow).on(subsetIsNat.asInstanceOf)
      val eq1 = have((isHeightFun(g), in(n, N), subset(m, n), in(x, app(g, m))) |- inTransRecFun(restrictedFunction(g, m))(x)) by Apply(equivalenceRevApply of (p1 := in(x, app(g, m)))).on(lastStep)

      have(subset(m, n) |- inTransRecFun(restrictedFunction(g, m))(x) ==> inTransRecFun(restrictedFunction(g, n))(x)) by Apply(transRecFunMonotonic).on(restrictedFunctionDomainMonotonic.asInstanceOf)
      have((isHeightFun(g), in(n, N), subset(m, n), inTransRecFun(restrictedFunction(g, m))(x)) |- in(x, app(g, n))) by Apply(equivalenceRevApply).on(lastStep, hasHeightBelow.asInstanceOf)
      have((isHeightFun(g), in(n, N), subset(m, n), in(x, app(g, m))) |- in(x, app(g, n))) by Cut(eq1, lastStep)
      thenHave((isHeightFun(g), in(n, N), subset(m, n)) |- in(x, app(g, m)) ==> in(x, app(g, n))) by Restate
      thenHave((isHeightFun(g), in(n, N), subset(m, n)) |- forall(x, in(x, app(g, m)) ==> in(x, app(g, n)))) by RightForall
      have((isHeightFun(g), in(n, N), subset(m, n)) |- subset(app(g, m), app(g, n))) by Apply(equivalenceRevApply).on(lastStep, subsetAxiom.asInstanceOf)
      have((isHeightFun(g), in(n, N)) |- in(m, successor(n)) ==> subset(app(g, m), app(g, n))) by Apply(lastStep).on(imp0)
      thenHave(thesis) by RightForall
    }

    val heightZero = Lemma(isHeightFun(g) |- !in(x, app(g, emptySet))) {
      have(isHeightFun(g) |- in(x, app(g, emptySet)) <=> inTransRecFun(restrictedFunction(g, emptySet))(x)) by Apply(hasHeightBelow).on(zeroIsNat.asInstanceOf)
      thenHave(isHeightFun(g) |- in(x, app(g, emptySet)) <=> inTransRecFun(emptySet)(x)) by Substitution.ApplyRules(restrictedFunctionEmptyDomain)
    }


    val succHeightWeak = Lemma((isHeightFun(g), in(n, N)) |- in(x, app(g, successor(n))) <=> inInductiveFun(app(g, n))(x)) {
      val restrFunNotEmpty = have(isHeightFun(g) |- !(restrictedFunction(g, successor(n)) === emptySet)) by Apply(restrictedFunctionNotEmpty).on(heightFunNonEmpty.asInstanceOf, zeroIsNotSucc.asInstanceOf)
      
      val unionRangeSubst = have((isHeightFun(g), in(n, N)) |- unionRange(restrictedFunction(g, successor(n))) === app(g, n)) by Apply(unionRangeLemma).on(heightFunCumulative.asInstanceOf)
      have((isHeightFun(g), in(n, N)) |- in(x, app(g, successor(n))) <=> inTransRecFun(restrictedFunction(g, successor(n)))(x)) by Apply(hasHeightBelow).on(equivalenceApply of (p1 := in(n, N)), successorIsNat.asInstanceOf)
      thenHave((isHeightFun(g), in(n, N)) |- in(x, app(g, successor(n))) <=> !(restrictedFunction(g, successor(n)) === emptySet) /\ inInductiveFun(app(g, n))(x)) by Substitution.ApplyRules(unionRangeSubst)
      have(thesis) by Tautology.from(lastStep, restrFunNotEmpty)
    }

    val heightFunUniqueness = Lemma(existsOne(g, isHeightFun(g))) {
      sorry
    }

    val heightFunUniqueness2 = Lemma((isHeightFun(f), isHeightFun(g)) |- f === g) {
      sorry
    }

    val heightFunExistence = Lemma(exists(g, isHeightFun(g))) {
      have(thesis) by Apply(existsOneImpliesExists of (P := lambda(g, isHeightFun(g)))).on(heightFunUniqueness.asInstanceOf)
    }

    def termDefinition(z: Term): Formula = forall(t, in(t, z) <=> forall(g, isHeightFun(g) ==> in(t, unionRange(g))))

    val termExistence = Lemma(existsOne(z, termDefinition(z))) {
      val heightFunUniqueness3 = have((isHeightFun(f), isHeightFun(g)) |- f === g) subproof {
        have(thesis) by Restate.from(heightFunUniqueness2)
      }

      have(exists(z, forall(t, in(t, z) <=> forall(g, isHeightFun(g) ==> in(t, unionRange(g)))))) subproof {
        have((isHeightFun(f), isHeightFun(g), in(t, unionRange(f))) |- in(t, unionRange(f))) by Restate
        thenHave((isHeightFun(f), isHeightFun(g), in(t, unionRange(f))) |- in(t, unionRange(g))) by Substitution.ApplyRules(heightFunUniqueness3)
        thenHave((isHeightFun(f), in(t, unionRange(f))) |- isHeightFun(g) ==> in(t, unionRange(g))) by Restate
        val sl = thenHave((isHeightFun(f), in(t, unionRange(f))) |- forall(g, isHeightFun(g) ==> in(t, unionRange(g)))) by RightForall

        have(forall(g, isHeightFun(g) ==> in(t, unionRange(g))) |- forall(g, isHeightFun(g) ==> in(t, unionRange(g)))) by Hypothesis
        thenHave(forall(g, isHeightFun(g) ==> in(t, unionRange(g))) |- isHeightFun(f) ==> in(t, unionRange(f))) by InstantiateForall(f)
        val sr = thenHave((forall(g, isHeightFun(g) ==> in(t, unionRange(g))), isHeightFun(f)) |- in(t, unionRange(f))) by Restate

        have(isHeightFun(f) |- in(t, unionRange(f)) <=> forall(g, isHeightFun(g) ==> in(t, unionRange(g)))) by Tautology.from(sl, sr)
        thenHave(isHeightFun(f) |- forall(t, in(t, unionRange(f)) <=> forall(g, isHeightFun(g) ==> in(t, unionRange(g))))) by RightForall
        thenHave(isHeightFun(f) |- exists(z, forall(t, in(t, z) <=> forall(g, isHeightFun(g) ==> in(t, unionRange(g)))))) by RightExists
        thenHave(exists(f, isHeightFun(f)) |- exists(z, forall(t, in(t, z) <=> forall(g, isHeightFun(g) ==> in(t, unionRange(g)))))) by LeftExists
        have(thesis) by Cut(heightFunExistence.asInstanceOf,lastStep)
      }
      have(thesis) by Apply(uniqueByExtension of (schemPred := lambda(t, forall(g, isHeightFun(g) ==> in(t, unionRange(g)))))).on(lastStep)
    }

    
    val term = FunctionDefinition(name, line.value, file.value)(typeVariables, z, forall(t, in(t, z) <=> forall(g, isHeightFun(g) ==> in(t, unionRange(g)))), termExistence).label

    val appliedTerm = term.applySeq(typeVariables)

    def apply(terms: Term*) = term.applySeq(terms)

    val inTerm = Lemma(isHeightFun(g) |- in(x, appliedTerm) <=> in(x, unionRange(g))) {
      val heightFunUniqueness3 = have((isHeightFun(f), isHeightFun(g)) |- f === g) subproof {
        have(thesis) by Restate.from(heightFunUniqueness2)
      }
      have((appliedTerm === appliedTerm) <=> termDefinition(appliedTerm)) by InstantiateForall(appliedTerm)(term.definition)
      thenHave(termDefinition(appliedTerm)) by Tautology
      val termDef = thenHave(in(x, appliedTerm) <=> forall(g, isHeightFun(g) ==> in(x, unionRange(g)))) by InstantiateForall(x)
      val termDefL = have(in(x, appliedTerm) |- forall(g, isHeightFun(g) ==> in(x, unionRange(g)))) by Apply(equivalenceApply).on(termDef)
      val termDefR = have(forall(g, isHeightFun(g) ==> in(x, unionRange(g))) |- in(x, appliedTerm)) by Apply(equivalenceRevApply).on(termDef)


      have(forall(g, isHeightFun(g) ==> in(x, unionRange(g))) |- forall(g, isHeightFun(g) ==> in(x, unionRange(g)))) by Hypothesis
      thenHave(forall(g, isHeightFun(g) ==> in(x, unionRange(g))) |- isHeightFun(g) ==> in(x, unionRange(g))) by InstantiateForall(g)
      thenHave((forall(g, isHeightFun(g) ==> in(x, unionRange(g))), isHeightFun(g)) |- in(x, unionRange(g))) by Restate

      val caseL = have((isHeightFun(g), in(x, appliedTerm)) |- in(x, unionRange(g))) by Apply(lastStep).on(termDefL)

      have((isHeightFun(f), isHeightFun(g), in(x, unionRange(g))) |- in(x, unionRange(g))) by Restate
      thenHave((isHeightFun(f), isHeightFun(g), in(x, unionRange(g))) |- in(x, unionRange(f))) by Substitution.ApplyRules(heightFunUniqueness3)
      thenHave((isHeightFun(g), in(x, unionRange(g))) |- isHeightFun(f) ==> in(x, unionRange(f))) by Restate
      thenHave((isHeightFun(g), in(x, unionRange(g))) |- forall(f, isHeightFun(f) ==> in(x, unionRange(f)))) by RightForall
      val caseR = have((isHeightFun(g), in(x, unionRange(g))) |- in(x, appliedTerm)) by Cut(lastStep, termDefR)

      have(thesis) by Tautology.from(caseL, caseR)

    }

    val termHasHeight = Lemma(isHeightFun(g) |- (in(x, appliedTerm) <=> ∃(n, in(n, N) /\ in(x, app(g, n))))) {
      val substDomain = have((relationDomain(g) === N) |- (relationDomain(g) === N)) by Hypothesis
      have((in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> (in(n, relationDomain(g)) /\ in(x, app(g, n)))) by Exact(equivalenceReflexivity)
      thenHave(isHeightFun(g) |- (in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> (in(n, N) /\ in(x, app(g, n)))) by Substitution.ApplyRules(substDomain)
      thenHave(isHeightFun(g) |- forall(n, (in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> (in(n, N) /\ in(x, app(g, n))))) by RightForall
      val rew = have(isHeightFun(g) |- exists(n, in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> exists(n, in(n, N) /\ in(x, app(g, n)))) by Apply(
        existentialEquivalenceDistribution of (P := lambda(n, in(n, relationDomain(g)) /\ in(x, app(g, n))), Q := lambda(n, in(n, N) /\ in(x, app(g, n))))
      ).on(lastStep)

      have(isHeightFun(g) |- (in(x, appliedTerm) <=> ∃(n, in(n, relationDomain(g)) /\ in(x, app(g, n))))) by Apply(equivalenceRewriting).on(unionRangeMembership.asInstanceOf, inTerm.asInstanceOf)
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, rew)
    }

    val termsHaveHeight = constructorMap.map((k, c) => k -> Lemma(isHeightFun(g) |- (consVarMembership(c, appliedTerm) <=> ∃(n, in(n, N) /\ consVarMembership(c, app(g, n))))) {
      
      val imp0 = have((isHeightFun(g), ∃(n, in(n, N) /\ consVarMembership(c, app(g, n)))) |- consVarMembership(c, appliedTerm)) subproof {
        val andSeq = for((v, ty) <- c.variables.zip(c.typeArgs)) yield
          ty match
            case Self => 
              have((isHeightFun(g), in(n, N) /\ in(v, app(g, n))) |- in(n, N) /\ in(v, app(g, n))) by Restate
              thenHave((isHeightFun(g), in(n, N) /\ in(v, app(g, n))) |- exists(n, in(n, N) /\ in(v, app(g, n)))) by RightExists
              have((isHeightFun(g), in(n, N) /\ in(v, app(g, n))) |- in(v, appliedTerm)) by Apply(equivalenceRevApply).on(lastStep, termHasHeight.asInstanceOf)
            case BaseType(t) =>
              have((isHeightFun(g), in(n, N) /\ in(v, t)) |- in(v, t)) by Restate
          thenHave((isHeightFun(g), in(n, N) /\ consVarMembership(c, app(g, n))) |- in(v, getTermOrElse(ty, appliedTerm))) by Weakening
          
        have((isHeightFun(g), in(n, N) /\ consVarMembership(c, app(g, n))) |- consVarMembership(c, appliedTerm)) by AndAggregate(andSeq)
        thenHave((isHeightFun(g), exists(n, in(n, N) /\ consVarMembership(c, app(g, n)))) |- consVarMembership(c, appliedTerm)) by LeftExists
      }

      val imp1 = have((isHeightFun(g), consVarMembership(c, appliedTerm)) |- ∃(n, in(n, N) /\ consVarMembership(c, app(g, n)))) subproof {
        sorry
        // /\ c.variables.zip(c.typeArgs).zipWithIndex.map(((v: Variable, ty: Type), i: Int) => 
        //   in(v, getTermOrElse(app(g, Variable(s"n$i"))))
        // )
      }

      have(thesis) by Tautology.from(imp0, imp1)
    })

    val heightConstructor = constructorMap.map((k, c) => k -> Lemma((isHeightFun(g), in(n, N)) |- consVarMembership(c, app(g, n)) ==> in(c.appliedTerm, app(g, successor(n)))) {
      
      val s0 = have(consVarMembership(c, app(g, n)) |- inInductiveFun(app(g, n))(c.appliedTerm)) by Restate.from(constructorInInductiveFun(k) of (s := app(g, n)))
      val s1 = have((isHeightFun(g), in(n, N)) |- in(c.appliedTerm, app(g, successor(n))) <=> inInductiveFun(app(g, n))(c.appliedTerm)) by Exact(succHeightWeak)
      
      have((isHeightFun(g), in(n, N), inInductiveFun(app(g, n))(c.appliedTerm),  in(c.appliedTerm, app(g, successor(n))) <=> inInductiveFun(app(g, n))(c.appliedTerm)) |- in(c.appliedTerm, app(g, successor(n)))) by Exact(equivalenceRevApply)
      have((isHeightFun(g), in(n, N), inInductiveFun(app(g, n))(c.appliedTerm)) |- in(c.appliedTerm, app(g, successor(n)))) by Cut(s1, lastStep)
      have((isHeightFun(g), in(n, N), consVarMembership(c, app(g, n))) |- in(c.appliedTerm, app(g, successor(n)))) by Cut(s0, lastStep)
    })

    val typing = constructorMap.map((k, c) => { k ->
      Lemma(removeConstants(consVarMembership(c, appliedTerm) ==> in(c.appliedTerm, appliedTerm))) {
    
      val succNIsTerm = have((isHeightFun(g), in(n, N), in(c.appliedTerm, app(g, successor(n)))) |- in(c.appliedTerm, appliedTerm)) subproof {
        have(in(n, N) |- in(successor(n), N)) by Apply(equivalenceApply).on(successorIsNat.asInstanceOf)
        val s0l = thenHave((isHeightFun(g), in(n, N), in(c.appliedTerm, app(g, successor(n)))) |- in(successor(n), N)) by Weakening

        val s0r = have((isHeightFun(g), in(n, N), in(c.appliedTerm, app(g, successor(n)))) |- in(c.appliedTerm, app(g, successor(n)))) by Restate
        have((isHeightFun(g), in(n, N), in(c.appliedTerm, app(g, successor(n)))) |- in(successor(n), N) /\ in(c.appliedTerm, app(g, successor(n)))) by RightAnd(s0l, s0r)
        thenHave((isHeightFun(g), in(n, N), in(c.appliedTerm, app(g, successor(n)))) |- exists(m, in(m, N) /\ in(c.appliedTerm, app(g, m)))) by RightExists
        have((isHeightFun(g), in(n, N), in(c.appliedTerm, app(g, successor(n)))) |- in(c.appliedTerm, appliedTerm)) by Apply(equivalenceRevApply).on(lastStep, termHasHeight.asInstanceOf)
      }

      have((isHeightFun(g), in(n, N), consVarMembership(c, app(g, n))) |- in(c.appliedTerm, app(g, successor(n)))) by Restate.from(heightConstructor(k))
      have((isHeightFun(g), in(n, N), consVarMembership(c, app(g, n))) |- in(c.appliedTerm, appliedTerm)) by Cut(lastStep, succNIsTerm)
      thenHave((isHeightFun(g), in(n, N) /\ consVarMembership(c, app(g, n))) |- in(c.appliedTerm, appliedTerm)) by Restate
      val s1 = thenHave((isHeightFun(g), exists(n, in(n, N) /\ consVarMembership(c, app(g, n)))) |- in(c.appliedTerm, appliedTerm)) by LeftExists
      have((isHeightFun(g), consVarMembership(c, appliedTerm)) |- exists(n, in(n, N) /\ consVarMembership(c, app(g, n)))) by Apply(equivalenceApply).on(termsHaveHeight(k).asInstanceOf)
      have((isHeightFun(g), consVarMembership(c, appliedTerm)) |- in(c.appliedTerm, appliedTerm)) by Cut(lastStep, s1)
      thenHave(isHeightFun(g) |- consVarMembership(c, appliedTerm) ==> in(c.appliedTerm, appliedTerm)) by Restate
      thenHave(exists(g, isHeightFun(g)) |- consVarMembership(c, appliedTerm) ==> in(c.appliedTerm, appliedTerm)) by LeftExists
      have(consVarMembership(c, appliedTerm) ==> in(c.appliedTerm, appliedTerm)) by Cut(heightFunExistence, lastStep)
      thenHave(thesis) by Restate
    }
  })

    
    lazy val succHeightStrong = Lemma((isHeightFun(g), in(n, N)) |- in(x, app(g, successor(n))) <=> isConstructor(x, app(g, n))) {

      val impl = have((isHeightFun(g), in(n, N), inInductiveFun(app(g, n))(x)) |- isConstructor(x, app(g, n))) subproof {
        
        def prop(n: Term) = inInductiveFun(app(g, n))(x) ==> isConstructor(x, app(g, n))
        
        have(inInductiveFun(app(g, emptySet))(x) |- isConstructor(x, app(g, emptySet)) \/ in(x, app(g, emptySet))) by Hypothesis
        val baseCase = have(isHeightFun(g) |- prop(emptySet)) by Tautology.from(lastStep, heightZero)
      
        val indThm = have((isHeightFun(g), prop(emptySet)) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Exact(natInduction of (P := lambda(k, prop(k))))
        val indPart0 = have(isHeightFun(g) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Cut(baseCase, indThm)
        
        val succInN = have(in(m, N) |- in(successor(m), N)) by Apply(equivalenceApply of (p1 := in(m, N))).on(successorIsNat.asInstanceOf)
        val succSuccInN = have(in(m, N) |- in(successor(successor(m)), N)) by Apply(equivalenceApply).on(succInN, successorIsNat.asInstanceOf)
        have(in(m, N) |- in(successor(m), successor(successor(m)))) by Apply(inSuccessor).on(succInN)
        val inSuccSucc = have(in(m, N) |- in(m, successor(successor(m)))) by Apply(natTransitive).on(lastStep, succSuccInN, inSuccessor.asInstanceOf)

        have((isHeightFun(g), in(m, N)) |- forall(k, in(k, successor(successor(m))) ==> subset(app(g, k), app(g, successor(m))))) by Apply(heightFunCumulative).on(succInN)
        thenHave((isHeightFun(g), in(m, N)) |- in(m, successor(successor(m))) ==> subset(app(g, m), app(g, successor(m)))) by InstantiateForall(m)
        have((isHeightFun(g), in(m, N)) |- subset(app(g, m), app(g, successor(m)))) by Apply(lastStep).on(inSuccSucc)
        have((isHeightFun(g), in(m, N)) |- forall(x, in(x, app(g, m)) ==> in(x, app(g, successor(m))))) by Apply(equivalenceApply).on(lastStep, subsetAxiom)
        val escalate0 = thenHave((isHeightFun(g), in(m, N)) |- in(y, app(g, m)) ==> in(y, app(g, successor(m)))) by InstantiateForall(y)

        
        val orSeq = 
          for c <- constructors yield
            val labelWithExVar = c.appliedTerm(exVar(c))

            val andSeq0 = 
              for (v, ty) <- exVar(c).zip(c.typeArgs) yield
                have((isHeightFun(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- in(v, getTermOrElse(ty, app(g, successor(m))))) by Weakening(escalate0 of (y := v))

            val s0l = have((isHeightFun(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- consExVarMembership(c, app(g, successor(m)))) by AndAggregate(andSeq0)
            val s0r = have((isHeightFun(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- labelWithExVar === x) by Restate

            have((isHeightFun(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- consExVarMembership(c, app(g, successor(m))) /\ (labelWithExVar === x)) by RightAnd(s0l, s0r)

            exVar(c).foldRight(lastStep) ( (v, acc) => 
                thenHave((isHeightFun(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- exists(v, acc.statement.right.head)) by RightExists
              )
            
            (exVar(c).foldRight((lastStep, consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x))) ( (v, acc) => 
                val (accFact, accSeq) = acc
                (thenHave((isHeightFun(g), in(m, N), exists(v, accSeq)) |- isConstructor(c, x, app(g, successor(m)))) by LeftExists, exists(v, accSeq))
              ))._1

            thenHave((isHeightFun(g), in(m, N), isConstructor(c, x, app(g, m))) |- isConstructor(x, app(g, successor(m)))) by Weakening
        

        
        val escalate1 = have((isHeightFun(g), in(m, N), isConstructor(x, app(g, m))) |- isConstructor(x, app(g, successor(m)))) by OrAggregate(orSeq)


        val s0 = have((isHeightFun(g), in(m, N), in(x, app(g, successor(m)))) |- inInductiveFun(app(g, m))(x)) by Apply(equivalenceApply of (p1 := in(x, app(g, successor(m))))).on(succHeightWeak.asInstanceOf)
        have(prop(m) |- prop(m)) by Hypothesis
        have((isHeightFun(g), in(m, N), in(x, app(g, successor(m))), prop(m)) |- isConstructor(x, app(g, m))) by Apply(lastStep).on(s0)
        have((isHeightFun(g), in(m, N), in(x, app(g, successor(m))), prop(m)) |- isConstructor(x, app(g, successor(m)))) by Cut(lastStep, escalate1)


        thenHave((isHeightFun(g), in(m, N), prop(m), inInductiveFun(app(g, successor(m)))(x)) |- isConstructor(x, app(g, successor(m)))) by Tautology
        thenHave((isHeightFun(g), in(m, N), prop(m)) |- prop(successor(m))) by Restate
        thenHave(isHeightFun(g) |- in(m, N) ==> (prop(m) ==> prop(successor(m)))) by Restate
        thenHave(isHeightFun(g) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m))))) by RightForall
        have(isHeightFun(g) |- forall(n, in(n, N) ==> prop(n))) by Apply(indPart0).on(lastStep)
        thenHave(isHeightFun(g) |- in(n, N) ==> prop(n)) by InstantiateForall(n)
        thenHave(thesis) by Restate
      }
      val impr = have((isHeightFun(g), in(n, N)) |- isConstructor(x, app(g, n)) ==> inInductiveFun(app(g, n))(x)) subproof {
        have(thesis) by Tautology
      }

      have((isHeightFun(g), in(n, N)) |- inInductiveFun(app(g, n))(x) <=> isConstructor(x, app(g, n))) by Tautology.from(impl, impr)
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, succHeightWeak.asInstanceOf)
    }

    def structuralInductionPrecond(c: Constructor): Formula =
      exVar(c).zip(c.typeArgs).foldRight[Formula](P(c.appliedTerm(exVar(c)))) ( (el, fc) =>
          val (v, ty) = el
          ty match
            case Self => forall(v, in(v, appliedTerm) ==> (P(v) ==> fc))
            case BaseType(t) => forall(v, in(v, t) ==> fc)
        )

    val structuralInduction = THM(constructors.foldRight[Formula](forall(x, in(x, appliedTerm) ==> P(x)))( (c, f) => structuralInductionPrecond(c) ==> f), s"${name} structural induction", line.value, file.value, Theorem)  {

      val preconditions = /\ (constructors.map(structuralInductionPrecond))
            
      def prop(n: Term) = forall(x, in(x, app(g, n)) ==> P(x)) 

      val baseCase = have(isHeightFun(g) |- prop(emptySet)) subproof {
        have(isHeightFun(g) |- in(x, app(g, emptySet)) ==> P(x)) by Weakening(heightZero)
        thenHave(thesis) by RightForall
      }

      val inductionThm = have((isHeightFun(g), prop(emptySet)) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Exact(natInduction of (P := lambda(k, prop(k))))
      val indPart0 = have(isHeightFun(g) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Cut(baseCase, inductionThm)
      
      val inductiveCase = have((isHeightFun(g), preconditions) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m))))) subproof {
        val orSeq = 
          (for (k, c) <- constructorMap yield

            val precond = structuralInductionPrecond(c)
            val labelWithExVar = c.appliedTerm(exVar(c))
            val consExVarMembershipAppGM = consExVarMembership(c, app(g, m))
            val consExVarMembershipAppGMEx = ∃(m, in(m, N) /\ consExVarMembership(c, app(g, m)))
            val consExVarMembershipTerm = consExVarMembership(c, appliedTerm)

            val consExVarMembershipAppGMToTerm = have((isHeightFun(g), in(m, N), consExVarMembershipAppGM) |- consExVarMembershipTerm) subproof {
              have((isHeightFun(g), in(m, N), consExVarMembershipAppGM) |- in(m, N) /\ consExVarMembershipAppGM) by Restate
              val consVarL = thenHave((isHeightFun(g), in(m, N), consExVarMembershipAppGM) |- consExVarMembershipAppGMEx) by RightExists
              val s0 = have(isHeightFun(g) |- consExVarMembershipTerm <=> consExVarMembershipAppGMEx) by Restate.from(termsHaveHeight(k).of(c.variables.zip(exVar(c)).map(_ := _) : _*))
              have((consExVarMembershipTerm <=> consExVarMembershipAppGMEx, consExVarMembershipAppGMEx) |- consExVarMembershipTerm) by Restate.from(equivalenceRevApply of (p1 := consExVarMembershipTerm, p2 := consExVarMembershipAppGMEx))
              val consVarR = have((isHeightFun(g), consExVarMembershipAppGMEx) |- consExVarMembershipTerm) by Cut(s0, lastStep)
              have(thesis) by Cut(consVarL, consVarR)
            }

            have((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- precond) by Restate


            exVar(c).zip(c.typeArgs).foldLeft(lastStep)( (fact, el) =>
              val ccl = fact.statement.right.head
              val (v, ty) = el

              ccl match
                case Forall(_, phi) => 
                  val instantiation = thenHave((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- phi) by InstantiateForall(v)
                  
                  phi match 
                    case Implies(membership, psi) => 
                      ty match
                        case Self => 
                          psi match
                            case Implies(_, theta) => 
                              have(prop(m) |- prop(m)) by Hypothesis
                              thenHave(prop(m) |- in(v, app(g, m)) ==> P(v)) by InstantiateForall(v)
                              val pv = thenHave((prop(m), consExVarMembershipAppGM) |- P(v)) by Weakening

                              have((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipTerm, consExVarMembershipAppGM, P(v)) |- theta) by Weakening(instantiation)
                              have((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipTerm, consExVarMembershipAppGM) |- theta) by Cut(pv, lastStep)
                              have((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- theta) by Cut(consExVarMembershipAppGMToTerm, lastStep)
                              
                            case _ => throw UnreachableException

                        case BaseType(t) =>
                          thenHave((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- psi) by Restate
                    case _ => throw UnreachableException
                case _ => throw UnreachableException
            )

            val substL = thenHave((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- P(labelWithExVar)) by Restate
            val substR = have((labelWithExVar === x, P(labelWithExVar)) |- P(x)) by Restate.from(substitutionThm of (x := labelWithExVar, y := x))
            have((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipAppGM, labelWithExVar === x) |- P(x)) by Cut(substL, substR)

            thenHave((isHeightFun(g), precond, in(m, N), prop(m), consExVarMembershipAppGM /\ (labelWithExVar === x)) |- P(x)) by Restate

            (exVar(c).foldRight((lastStep, consExVarMembershipAppGM /\ (labelWithExVar === x))) ( (v, acc) => 
              val (accFact, accSeq) = acc
              (thenHave((isHeightFun(g), precond, in(m, N), prop(m), exists(v, accSeq)) |- P(x)) by LeftExists, exists(v, accSeq))
            ))._1

            thenHave((isHeightFun(g), preconditions, in(m, N), prop(m), isConstructor(c, x, app(g, m))) |- P(x)) by Weakening).toSeq

        val appsucc = have((isHeightFun(g), in(m, N), in(x, app(g, successor(m)))) |- isConstructor(x, app(g, m))) by Apply(equivalenceApply).on(succHeightStrong.asInstanceOf)

        have((isHeightFun(g), preconditions, in(m, N), prop(m), isConstructor(x, app(g, m))) |- P(x)) by OrAggregate(orSeq)
        have((isHeightFun(g), preconditions, in(m, N), prop(m), in(x, app(g, successor(m)))) |- P(x)) by Apply(lastStep).on(appsucc)
        thenHave((isHeightFun(g), preconditions, in(m, N), prop(m)) |- in(x, app(g, successor(m))) ==> P(x)) by Restate


        have((isHeightFun(g), preconditions, in(m, N), prop(m), in(x, app(g, successor(m)))) |- P(x)) by Apply(lastStep).on(appsucc)
        thenHave((isHeightFun(g), preconditions, in(m, N), prop(m)) |- in(x, app(g, successor(m))) ==> P(x)) by Restate

        thenHave((isHeightFun(g), preconditions, in(m, N), prop(m)) |- prop(successor(m))) by RightForall
        thenHave((isHeightFun(g), preconditions) |- in(m, N) ==> (prop(m) ==> prop(successor(m)))) by Restate
        thenHave(thesis) by RightForall
      }


      have((isHeightFun(g), preconditions) |- forall(n, in(n, N) ==> prop(n))) by Apply(indPart0).on(lastStep)
      thenHave((isHeightFun(g), preconditions) |- in(n, N) ==> prop(n)) by InstantiateForall(n)
      thenHave((isHeightFun(g), preconditions, in(n, N)) |- prop(n)) by Restate
      thenHave((isHeightFun(g), preconditions, in(n, N)) |- in(x, app(g, n)) ==> P(x)) by InstantiateForall(x)
      thenHave((isHeightFun(g), preconditions, in(n, N) /\ in(x, app(g, n))) |- P(x)) by Restate
      val exImpliesP = thenHave((isHeightFun(g), preconditions, exists(n, in(n, N) /\ in(x, app(g, n)))) |- P(x)) by LeftExists
      have((isHeightFun(g), in(x, appliedTerm)) |- exists(n, in(n, N) /\ in(x, app(g, n)))) by Apply(equivalenceApply of (p1 := in(x, appliedTerm))).on(termHasHeight.asInstanceOf)

      have((isHeightFun(g), preconditions, in(x, appliedTerm)) |- P(x)) by Cut(lastStep, exImpliesP)
      thenHave((exists(g, isHeightFun(g)), preconditions, in(x, appliedTerm)) |- P(x)) by LeftExists
      have(preconditions |- in(x, appliedTerm) ==> P(x)) by Apply(lastStep).on(heightFunExistence.asInstanceOf)
      thenHave(preconditions |- forall(x, in(x, appliedTerm) ==> P(x))) by RightForall
      thenHave(thesis) by Restate
    }

    val patternMatching = THM(in(x, appliedTerm) |- removeConstants(isConstructor(x, appliedTerm)), s"${name} pattern constructors", line.value, file.value, Theorem) {

      def ineqPrecond(c: Constructor): Formula =
        exVar(c).zip(c.typeArgs).foldRight[Formula](!(x === c.appliedTerm(exVar(c)))) ( (el, fc) =>
            val (v, ty) = el
            ty match
              case Self => forall(v, in(v, appliedTerm) ==> (!(x === v) ==> fc))
              case BaseType(t) => forall(v, in(v, t) ==> fc)
        )

      val preconditions = /\ (constructors.map(ineqPrecond))


      def negIneqPrecond(c: Constructor): Formula =
        exVar(c).zip(c.typeArgs).foldRight[Formula](x === c.appliedTerm(exVar(c))) ( (el, fc) =>
            val (v, ty) = el
            ty match
              case Self => exists(v, in(v, appliedTerm) /\ (!(x === v) /\ fc))
              case BaseType(t) => exists(v, in(v, t) /\ fc)
        )

      val negPreconditions = \/ (constructors.map(negIneqPrecond))

      def negWeakIneqPrecond(c: Constructor): Formula =
        exVar(c).zip(c.typeArgs).foldRight[Formula](c.appliedTerm(exVar(c)) === x) ( (el, fc) =>
            val (v, ty) = el
            exists(v, in(v, getTermOrElse(ty, appliedTerm)) /\ fc)
        )

      val orSeq = 
        for c <- constructors yield
          val s0l = have(negIneqPrecond(c) |- negWeakIneqPrecond(c)) subproof {
            have(x === c.appliedTerm(exVar(c)) |- c.appliedTerm(exVar(c)) === x) by Restate

            exVar(c).zip(c.typeArgs).foldRight(lastStep)( (el, fact) =>
              val (v, ty) = el
              val left = fact.statement.left.head
              val right = fact.statement.right.head

              val newLeft =
                ty match
                  case Self => 
                    thenHave(!(x === v) /\ left |- right) by Weakening
                    !(x === v) /\ left
                  case _ => left

              val weakr = thenHave(in(v, getTermOrElse(ty, appliedTerm)) /\ left |- right) by Weakening
              val weakl = have(in(v, getTermOrElse(ty, appliedTerm)) /\ left |- in(v, getTermOrElse(ty, appliedTerm))) by Restate

              have(in(v, getTermOrElse(ty, appliedTerm)) /\ left |- in(v, getTermOrElse(ty, appliedTerm)) /\ right) by RightAnd(weakl, weakr)
              thenHave(in(v, getTermOrElse(ty, appliedTerm)) /\ left |- exists(v, in(v, getTermOrElse(ty, appliedTerm)) /\ right)) by RightExists
              thenHave(exists(v, in(v, getTermOrElse(ty, appliedTerm)) /\ left) |- exists(v, in(v, getTermOrElse(ty, appliedTerm)) /\ right)) by LeftExists
            )

          }
          val s0r = have(negWeakIneqPrecond(c) |- isConstructor(c, x, appliedTerm)) by Tableau
          have(negIneqPrecond(c) |- isConstructor(c, x, appliedTerm)) by Cut(s0l, s0r)
          thenHave(negIneqPrecond(c) |- isConstructor(x, appliedTerm)) by Weakening
      
      val weaken = have(negPreconditions |- isConstructor(x, appliedTerm)) by OrAggregate(orSeq)

      have(preconditions |- forall(z, in(z, appliedTerm) ==> !(x === z))) by Exact(structuralInduction of (P := lambda(z, !(x === z))))
      thenHave(preconditions |- in(x, appliedTerm) ==> !(x === x)) by InstantiateForall(x)
      val ind = thenHave(preconditions |- !in(x, appliedTerm)) by Restate
      thenHave(!negPreconditions |- !in(x, appliedTerm)) by Restate
      thenHave(in(x, appliedTerm) |- negPreconditions) by Restate


      

      have(in(x, appliedTerm) |- isConstructor(x, appliedTerm)) by Cut(lastStep, weaken)
      thenHave(thesis) by Restate
    }

  
    val totalTime = (System.nanoTime - before) / 1000000
    println(s"Total time: $totalTime ms")
  }

    class TypedConstructor(using line: sourcecode.Line, file: sourcecode.File)(val inner: Constructor, adt: UntypedADT)  {

    val fullName = s"${adt.name}/${inner.name}"

    val typeVariables = adt.typeVariables
    val typeArity = typeVariables.length

    val typeArgs = inner.typeArgs.map{
      case Self => adt.appliedTerm
      case BaseType(t) => t
    }

    val typ = typeArgs.foldRight[Term](adt.appliedTerm)((a, b) => a |=> b) 

    def appSeq(f: Term)(args: Seq[Term]): Term = args.foldLeft(f)((acc, v) => f * v)
    def appSeq(f: Term): Term = appSeq(f)(inner.variables)

    val untypedFunctionalDefinition = (c :: typ) /\ inner.variables.foldRight(appSeq(c) === inner.appliedTerm)(forall(_, _))
    val untypedFunctionalUniqueness = Lemma(existsOne(c, untypedFunctionalDefinition)) {
      sorry
    }


    val untypedFunctional = FunctionDefinition(fullName, line.value, file.value)(typeVariables, c, untypedFunctionalDefinition, untypedFunctionalUniqueness).label

    val typing = Axiom(typeVariables.foldRight[Formula](untypedFunctional.applySeq(typeVariables) :: typ)(forall(_, _)))
    val typedFunctional = TypedConstantFunctional(fullName, typeArity, FunctionalClass(Seq.fill(typeArity)(any), typeVariables, typ, typeArity), typing)

    def apply(terms: Term*) = typedFunctional.applySeq(terms)
    
    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
     *
     * e.g. Cons(head1, tail1) === Cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
     */
    val injectivity1 =

      val tappterm = untypedFunctional.applySeq(typeVariables)

      // variable sequences x_0, ..., x_n-1 and y_0, ..., y_n-1
      val xs = for i <- 0 until inner.arity yield Variable(s"x${i}")
      val ys = for i <- 0 until inner.arity yield Variable(s"y${i}")
      val tappFun = untypedFunctional.applySeq(typeVariables)
      val tappterm1 = appSeq(tappFun)(xs)
      val tappterm2 = appSeq(tappFun)(ys)

      if inner.arity == 0 then
          Theorem(tappterm1 === tappterm2) {
            have(thesis) by Restate
          }
      else 
          Theorem((tappterm1 === tappterm2) <=> /\ (xs.zip(ys).map(_ === _))) {

            val txs = inner.appliedTerm(xs)
            val tys = inner.appliedTerm(ys)

            

            have(forall(c, (tappFun === c) <=> ((c :: typ) /\ inner.variables.foldRight(appSeq(c) === inner.appliedTerm)(forall(_, _))))) by Exact(untypedFunctional.definition)
            thenHave((tappFun === tappFun) <=> ((tappFun :: typ) /\ inner.variables.foldRight(appSeq(tappFun) === inner.appliedTerm)(forall(_, _)))) by InstantiateForall(tappFun)
            val tappFunDef = thenHave(inner.variables.foldRight(appSeq(tappFun) === inner.appliedTerm)(forall(_, _))) by Tautology

            xs.zip(inner.variables).foldLeft(tappFunDef)((fact, p) => 
              val (x, v) = p
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi.substitute(v := x)) by InstantiateForall(x)
                case _ => throw UnreachableException   
            )
            val tappTerm1Def = thenHave(tappterm1 === txs) by Restate

            have(tappFunDef.statement) by Restate.from(tappFunDef)

            ys.zip(inner.variables).foldLeft(tappFunDef)((fact, p) => 
              val (y, v) = p
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi.substitute(v := y)) by InstantiateForall(y)
                case _ => throw UnreachableException   
            )
            val tappTerm2Def = thenHave(tappterm2 === tys) by Restate

            val tappTerm1DefFlipped = have(txs === tappterm1) by Restate.from(tappTerm1Def)
            val tappTerm2DefFlipped = have(tys === tappterm2) by Restate.from(tappTerm2Def)

            have(tappterm1 === tappterm2 |- tappterm1 === tys) by Apply(equalityTransitivity of (y := tappterm2)).on(tappTerm2Def)
            val imp1 = have(tappterm1 === tappterm2 |- txs === tys) by Apply(equalityTransitivity).on(tappTerm1DefFlipped, lastStep)

            have(txs === tys |- tappterm1 === tys) by Apply(equalityTransitivity of (y := txs)).on(tappTerm1Def)
            val imp2 = have(txs === tys |- tappterm1 === tappterm2) by Apply(equalityTransitivity).on(tappTerm2DefFlipped, lastStep)

            have((tappterm1 === tappterm2) <=> (txs === tys)) by Tautology.from(imp1, imp2)
            have(thesis) by Apply(equivalenceRewriting).on(lastStep, inner.injectivityThm.asInstanceOf)
          }
  
    
  }

  class TypedADT(val inner: UntypedADT, val constructors: Seq[TypedConstructor]) {

    def apply(terms: Term*) = inner.term.applySeq(terms)


    def injectivity2(c1: TypedConstructor, c2: TypedConstructor) =
      require(c1.inner.tag != c2.inner.tag, "The given constructors must be different.")

      val tappFunC1 = c1.untypedFunctional.applySeq(c1.typeVariables)
      val tappFunC2 = c2.untypedFunctional.applySeq(c2.typeVariables)
      val appC1 = c1.appSeq(tappFunC1)
      val appC2 = c2.appSeq(tappFunC2)
      val t1 = c1.inner.appliedTerm
      val t2 = c2.inner.appliedTerm
      val tagTerm1 = c1.inner.tagTerm
      val tagTerm2 = c2.inner.tagTerm

      Theorem(!(appC1 === appC2)) {

        val diffTag = have(!(tagTerm1 === tagTerm2)) subproof {
          val tag1 = c1.inner.tag
          val tag2 = c2.inner.tag

          val minTag: Int = Math.min(tag1, tag2)
          val maxTag: Int = Math.max(tag1, tag2)

          val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Restate

          (1 to minTag).foldLeft(start)((fact, i) => 
            val midMaxTag = toTerm(maxTag - i)
            val midMinTag = toTerm(minTag - i)

            have(successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag) by Apply(equivalenceApply).on(successorInjectivity.asInstanceOf)
            have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
          )

          val chainInjectivity = thenHave(!(toTerm(maxTag - minTag) === emptySet) |- !(tagTerm1 === tagTerm2)) by Restate

          have(!(toTerm(maxTag - minTag) === emptySet)) by Exact(zeroIsNotSucc)
          have(!(tagTerm1 === tagTerm2)) by Cut(lastStep, chainInjectivity)
        }
        
        val defUnfolding = have(appC1 === appC2 |- t1 === t2) subproof {
          have(forall(c, (tappFunC1 === c) <=> ((c :: c1.typ) /\ c1.inner.variables.foldRight(c1.appSeq(c) === t1)(forall(_, _))))) by Exact(c1.untypedFunctional.definition)
          thenHave((tappFunC1 === tappFunC1) <=> ((tappFunC1 :: c1.typ) /\ c1.inner.variables.foldRight(appC1 === t1)(forall(_, _)))) by InstantiateForall(tappFunC1)
          thenHave(c1.inner.variables.foldRight(appC1 === t1)(forall(_, _))) by Tautology

          c1.inner.variables.foldLeft(lastStep)((fact, v) => 
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi.substitute(v := x)) by InstantiateForall(x)
              case _ => throw UnreachableException   
          )
          val tappTerm1Def = thenHave(t1 === appC1) by Restate

          have(forall(c, (tappFunC2 === c) <=> ((c :: c2.typ) /\ c2.inner.variables.foldRight(c2.appSeq(c) === t2)(forall(_, _))))) by Exact(c2.untypedFunctional.definition)
          thenHave((tappFunC2 === tappFunC2) <=> ((tappFunC2 :: c2.typ) /\ c2.inner.variables.foldRight(appC2 === t2)(forall(_, _)))) by InstantiateForall(tappFunC2)
          thenHave(c2.inner.variables.foldRight(appC2 === t2)(forall(_, _))) by Tautology

          c2.inner.variables.foldLeft(lastStep)((fact, v) => 
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException   
          )
          val tappTerm2Def = thenHave(appC2 === t2) by Restate

          have(appC1 === appC2 |- appC1 === t2) by Apply(equalityTransitivity of (y := appC2)).on(tappTerm2Def)
          val imp1 = have(appC1 === appC2 |- t1 === t2) by Apply(equalityTransitivity).on(tappTerm1Def, lastStep)
        }

        have(t1 === t2 |- (tagTerm1 === tagTerm2) /\ (c1.inner.subterm === c2.inner.subterm)) by Apply(equivalenceRevApply).on(pairExtensionality of (a := tagTerm1, b := c1.inner.subterm, c := tagTerm2, d := c2.inner.subterm))
        thenHave(!(tagTerm1 === tagTerm2) |- !(t1 === t2)) by Weakening

        have(!(t1 === t2)) by Cut(diffTag, lastStep)
        thenHave(t1 === t2 |- ()) by Restate

        have(appC1 === appC2 |- ()) by Cut(defUnfolding, lastStep)
      }

    val induction = inner.structuralInduction


  
  }


 
  object ADTSyntax {

    protected trait ConstructorConverter[T] {
      def apply(t: T): ConstructorBuilder
    }

    given unit_to_const: ConstructorConverter[Unit] with {
      override def apply(u: Unit): ConstructorBuilder = ConstructorBuilder.empty
    }

    given empty_to_const: ConstructorConverter[EmptyTuple] with {
      override def apply(t: EmptyTuple): ConstructorBuilder = ConstructorBuilder.empty
    }

    given tuple_to_const[H <: Type, T <: Tuple](using ConstructorConverter[T]): ConstructorConverter[H *: T] with {
      override def apply(t: H *: T): ConstructorBuilder = type_to_const(t.head) ++ any_to_const(t.tail)
    }

    given adt_tuple_to_const[H <: ADT, T <: Tuple](using ConstructorConverter[T]): ConstructorConverter[H *: T] with {
          override def apply(t: H *: T): ConstructorBuilder = adt_to_const(t.head) ++ any_to_const(t.tail)
    }

    given term_tuple_to_const[H <: Term, T <: Tuple](using ConstructorConverter[T]): ConstructorConverter[H *: T] with {
            override def apply(t: H *: T): ConstructorBuilder = term_to_const(t.head) ++ any_to_const(t.tail)
    }

    

    given type_to_const: ConstructorConverter[Type] with {
      override def apply(t: Type): ConstructorBuilder = ConstructorBuilder(t)
    }

    given adt_to_const: ConstructorConverter[ADT] with {
      override def apply(a: ADT): ConstructorBuilder = ConstructorBuilder(Self)
    }

    given term_to_const: ConstructorConverter[Term] with {
        override def apply(te: Term): ConstructorBuilder = ConstructorBuilder(BaseType(te))
    }

    given ConstructorConverter[Seq[Type]] with {
      override def apply(s: Seq[Type]): ConstructorBuilder = ConstructorBuilder(s: _*)
    }

    def any_to_const[T](any: T)(using c: ConstructorConverter[T]): ConstructorBuilder = c(any)

    extension [T1](left: T1)(using ConstructorConverter[T1]) {
      infix def |[T2](right: T2)(using ConstructorConverter[T2]): ADTBuilder = any_to_const(left) | any_to_const(right)
    }



    protected trait VariableSeqConverter[T] {
      def apply(t: T): Seq[Variable]
    }

    given unit_to_varseq: VariableSeqConverter[Unit] with {
      override def apply(u: Unit): Seq[Variable] = Seq.empty
    }

    given empty_to_varseq: VariableSeqConverter[EmptyTuple] with {
      override def apply(t: EmptyTuple): Seq[Variable] = Seq.empty
    }

    given tuple_to_varseq[H <: Variable, T <: Tuple](using VariableSeqConverter[T]): VariableSeqConverter[H *: T] with {
      override def apply(t: H *: T): Seq[Variable] = t.head +: any_to_varseq(t.tail)
    }

    given var_to_varseq: VariableSeqConverter[Variable] with {
      override def apply(v: Variable): Seq[Variable] = Seq[Variable](v)
    }

    def any_to_varseq[T](any: T)(using c: VariableSeqConverter[T]): Seq[Variable] = c(any)

    extension [T1](left: T1)(using VariableSeqConverter[T1]) {
      infix def ->(right: Term): (Seq[Variable], Term) = (any_to_varseq(left), right)
    }

    object ADTBuilder {
      def empty: ADTBuilder = apply(Seq())
    }

    object ConstructorBuilder {
      def empty: ConstructorBuilder = ConstructorBuilder()
    }

    case class ConstructorBuilder(param: Type*) {
      infix def | (b: ConstructorBuilder): ADTBuilder = this | ADTBuilder(Seq(b))
      infix def | (b: ADTBuilder): ADTBuilder = ADTBuilder(this +: b.inner )
      infix def ++ (b: ConstructorBuilder): ConstructorBuilder = ConstructorBuilder((param.toSeq ++ b.param.toSeq): _*)
    }

    case class ADTBuilder(inner: Seq[ConstructorBuilder]) {
      infix def | (b: ADTBuilder): ADTBuilder = ADTBuilder(inner ++ b.inner)
      infix def | (b: ConstructorBuilder): ADTBuilder = ADTBuilder(inner :+ b)
      infix def | (u: Unit): ADTBuilder = this | any_to_const(u)
      infix def | (t: Type): ADTBuilder = this | any_to_const(t)
      infix def | (s: Seq[Type]): ADTBuilder = this | any_to_const(s)
      infix def | (t: EmptyTuple): ADTBuilder = this | any_to_const(t)
      infix def | [T <: Tuple](t: Type *: T)(using c: ConstructorConverter[T]): ADTBuilder = this | (any_to_const(t.head) ++ any_to_const(t.tail))

      val signature: Seq[Signature] = inner.zipWithIndex.map((c, i) => (s"Constructor$i", c.param))

  }

    case class constructors(c: TypedConstructor *)

    type Signature = (String, Seq[Type])
    object ADT {
      def apply(name: String, sig: Signature*): (TypedADT, constructors) =
        val untypedConstructors = 
          for s <- sig yield
            val (consName, types) = s
            Constructor(consName, types)

        val untypedADT = new UntypedADT(name, untypedConstructors)

        val typedConstructors = 
          for c <- untypedConstructors yield
            TypedConstructor(c, untypedADT)
        
        (TypedADT(untypedADT, typedConstructors), constructors(typedConstructors: _*))


    }

    type ADT = TypedADT


    object define {
      var adtCounter = 0
      def unapply(using name: sourcecode.FullName)(builder: ADTBuilder): (TypedADT, constructors) =
        adtCounter = adtCounter + 1
        ADT(s"ADT$adtCounter", builder.signature: _*)

      def unapply(using name: sourcecode.FullName)(builder: Unit): (TypedADT, constructors) = unapply(ADTBuilder(Seq(unit_to_const(builder))))
      def unapply(using name: sourcecode.FullName)(builder: Term): (TypedADT, constructors) = unapply(ADTBuilder(Seq(term_to_const(builder))))
      def unapply(using name: sourcecode.FullName)(builder: Type): (TypedADT, constructors) = unapply(ADTBuilder(Seq(type_to_const(builder))))
      def unapply(using name: sourcecode.FullName)(builder: ADT): (TypedADT, constructors) = unapply(ADTBuilder(Seq(adt_to_const(builder))))
    }

    // ? WIP
    // object ADT {
    // object Case {
    //   def apply(c: Constructor)(f: (Seq[Variable], Term)): Case = new Case(c)(f)
    //   def apply(c: Constructor)(f: => Term): Case = new Case(c)((Seq.empty, f))
    // }

    // case class Case(c: Constructor)(f: (Seq[Variable], Term)) {
    //   //def apply(args: Term *): Term = f(args: _*)
    // }

    // // val mirror: Term = constructors(tree) (
    // //   Case(leaf){
    // //     leaf()
    // //   }, 
    // //   Case(node) {
    // //     (l, r) -> node(app(mirror, r), app(mirror, l))
    // //   }
    // // )

  }

    

  

}

object HOLTest extends lisa.HOL{

  import ADTTactic.*
  import ADTSyntax.*

    val x = typedvar(𝔹)

    val typ = variable

    val define(list: ADT, constructors(nil, cons)) = () | (typ, list)
    val define(list2: ADT, constructors(nil2, cons2)) = () | (typ, list(list(typ)))
    val define(truth: ADT, constructors(truthCons)) = ()
    val define(adt1: ADT, constructors(c1)) = emptySet
    val define(adt2: ADT, constructors(c2)) = list(𝔹)


    val typecheckNil = TypingTheorem(nil(𝔹) :: list(𝔹))
    val typecheckCons = TypingTheorem(cons(𝔹) :: (𝔹 |=> (list(𝔹) |=> list(𝔹))))
    val typecheckNil2 = TypingTheorem(nil(list(𝔹)) :: list(list(𝔹)))

    show(list.injectivity2(nil, cons))
    

  }
