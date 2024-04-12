package lisa.maths.settheory.types.adt

/**
  * Tactic that proves every goal of the form:
  *
  * ` ... |- ..., ∀x1, ..., xn. P(x), ...`
  * 
  * ` ..., ∀x1, ..., xn . P(x), ... |- ...`
  * 
  * ` ... |- ..., ∃x1, ..., xn. P(x), ...`
  * 
  * ` ..., ∃x1, ..., xn . P(x), ... |- ...`
  * 
  * given a proof of the sequents without quantification.
  */
object QuantifiersIntro extends lisa.prooflib.ProofTacticLib.ProofTactic {

  import lisa.prooflib.SimpleDeducedSteps.Restate
  import lisa.prooflib.BasicStepTactic.*
  import lisa.fol.FOL.*

  /**
    * Executes the tactic on a specific goal.
    *
    * @param lib the library that is currently being used
    * @param proof the ongoing proof in which the tactic is called
    * @param vars the variables that needs to be quantified
    * @param fact the proof of the sequent without quantification
    * @param bot the statement to prove
    */
  def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(vars: Seq[Variable])(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
    TacticSubproof { sp ?=>
      if vars.isEmpty then
        lib.have(bot) by Restate.from(fact)
      else
        val diff: Sequent = bot -- fact.statement

        diff match
          case Sequent(s, _) if s.size == 1 =>
            val diffRest = bot.left -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.left -- diffRest).head
            f match
              case BinderFormula(Forall, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = forall(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = exists(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftExists(accFact), newFormula)
                )
              case _ => return proof.InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(_, s) if s.size == 1 =>
            val diffRest = bot.right -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.right -- diffRest).head
            f match
              case BinderFormula(Forall, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = forall(v, accFormula)
                  (lib.have(bot.left |- diffRest + newFormula) by RightForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = exists(v, accFormula)
                  (lib.have(bot.left |- diffRest + newFormula) by RightExists(accFact), newFormula)
                )
              case _ => return proof.InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty => lib.have(bot) by Restate.from(fact)
          case _ => return proof.InvalidProofTactic("Two or more formulas in the sequent have changed.")

          
    }  
}

/**
 * General purpose helpers.
 */
private [adt] object Helpers {

  import lisa.fol.FOL.{*, given}

  /**
    * Benchmarks a block of code.
    *
    * @param name the name of the benchmark
    * @param f the block of code to benchmark
    * @return the result of the block of code and prints how long it took to execute
    */
  def benchmark[T](name: String)(f: => T): T = {
    val before = System.nanoTime

    val res = f

    val totalTime = (System.nanoTime - before) / 1000000

    println(s"$name time: $totalTime ms")

    res
  }

  /**
    * Exception thrown when code that should not be accessed is reached.
    */
  object UnreachableException extends Exception("This code should not be accessed. If you see this message, please report it to the library maintainers.")

  // *********************
  // * FIRST ORDER LOGIC *
  // *********************

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
  val schemPred = predicate[1]

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


  /**
   * Picks fresh variables starting with a given prefix .
   * 
   * @param prefix the prefix of the fresh variables
   * @param size the number of fresh variables to output
   * @param assigned the variables that are already used
   * @param counter the index to append to the prefix
   * @param acc the variables that have already been generated by this method
   * 
   */
  def chooseVars(prefix: String, size: Int, assigned: Set[Variable] = Set.empty, counter: Int = 0, acc: Seq[Variable] = Seq.empty): Seq[Variable] =
    if size == 0 then 
      acc
    else
      val newVar = Variable(s"${prefix}${counter}")
      if assigned.contains(newVar) then
        chooseVars(prefix, size, assigned, counter + 1, acc)
      else 
        chooseVars(prefix, size - 1, assigned, counter + 1, acc :+ newVar)


}

/**
  * Definitions and helper functions for ADT.
  */
private[adt] object ADTDefinitions {

  import lisa.maths.settheory.SetTheory.*
  import lisa.maths.settheory.types.TypeSystem.*
  import Helpers.{/\}

  /**
   * The specification of a constructor can either contain terms or a self reference, i.e. a reference to the ADT itself.
   */
  trait ConstructorArgument 
  
  /**
   * A symbol for self reference
   */
  case object Self extends ConstructorArgument

  /**
    * Syntactic represenation of a term
    *
    * @param t the underlying term
    */
  case class GroundType(t: Term) extends ConstructorArgument

  /**
   * Returns the term associated to a constructor argument, or in case it is a self reference, returns the term associated to the ADT.
   *
   * @param arg the constructor argument
   * @param adt the term representing the ADT
   */
  def getOrElse(arg: ConstructorArgument, adt: Term): Term =
    arg match {
      case Self => adt
      case GroundType(term) => term
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

  /**
    * Returns a sequence of formulas asserting that all terms of a sequence are well-typed. 
    *
    * @param s the terms and their respective types
    */
  def wellTyped(s: Seq[(Term, Term)]): Seq[Formula] = s.map(_ :: _)

    /**
    * Returns a sequence of formulas asserting that all terms of a sequence are well-typed with respect to the
    * specification of a constructor. 
    *
    * @param s the terms and their respective type
    * @param orElse the term to use in case of a self reference
    */
  def wellTyped(s: Seq[(Term, ConstructorArgument)])(orElse: Term): Seq[Formula] = s.map((t, arg) => t :: getOrElse(arg, orElse))

  /**
   * Returns a set of formulas asserting that all terms of a sequence are well-typed. 
   * 
   * @param s the terms and their respective types
   */
  def wellTypedSet(s: Seq[(Term, Term)]): Set[Formula] = wellTyped(s).toSet

    /**
    * Returns a set of formulas asserting that all terms of a sequence are well-typed with respect to the
    * specification of a constructor. 
    *
    * @param s the terms and their respective type
    * @param orElse the term to use in case of a self reference
    */
  def wellTypedSet(s: Seq[(Term, ConstructorArgument)])(orElse: Term): Set[Formula] = wellTyped(s)(orElse).toSet

  /**
   * Returns a formula asserting that all terms of a sequence are well-typed. 
   * 
   * @param s the terms and their respective types
   */
  def wellTypedFormula(s: Seq[(Term, Term)]): Formula = /\ (wellTyped(s))

  /**
    * Returns a formula asserting that all terms of a sequence are well-typed with respect to the
    * specification of a constructor. 
    *
    * @param s the terms and their respective type
    * @param orElse the term to use in case of a self reference
    */
  def wellTypedFormula(s: Seq[(Term, ConstructorArgument)])(orElse: Term): Formula = /\ (wellTyped(s)(orElse))

}


/**
 * List of external set theoretic theorems needed for proofs about ADT.
 * Some of these theorems are not yet implemented in the library and
 * will be added in the future.
 */
private [adt] object ADTHelperTheorems {

  import lisa.maths.settheory.SetTheory.{*, given}
  import lisa.maths.Quantifiers.{existentialEquivalenceDistribution, equalityInExistentialQuantifier,
    existentialConjunctionWithClosedFormula, equalityTransitivity}
  import ADTDefinitions.*
  import Helpers.*
  //import lisa.maths.Quantifiers.*

  // TODO: Remove
  val pair = ConstantFunctionLabel("pair", 2)
  addSymbol(pair)

  val pairExtensionality = Lemma((pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))) {
    sorry
  }

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
  val leftImpliesEquivalenceWeak = Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2)) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- Implication distributes over equivalence.
   */
  val leftImpliesEquivalenceStrong = Lemma(p ==> (p1 <=> p2) |- (p ==> p1) <=> (p ==> p2)) {
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
   * Theorem --- The range of the empty relation is empty.
   * 
   *     `range(∅) = ∅`
   * 
   */
  val rangeEmpty = Theorem(relationRange(emptySet) === emptySet) {
    import lisa.maths.settheory.SetTheory

    have(!in(SetTheory.pair(a, t), emptySet)) by Exact(emptySetAxiom)
    thenHave(forall(a, !in(SetTheory.pair(a, t), emptySet))) by RightForall
    val s0 = thenHave(!exists(a, in(SetTheory.pair(a, t), emptySet))) by Restate

    have(!in(t, emptySet)) by Exact(emptySetAxiom)
    have(in(t, emptySet) <=> exists(a, in(SetTheory.pair(a, t), emptySet))) by Tautology.from(lastStep, s0)
    val defRHS = thenHave(forall(t, in(t, emptySet) <=> exists(a, in(SetTheory.pair(a, t), emptySet)))) by RightForall

    have((relationRange(emptySet) === emptySet) <=> forall(t, in(t, emptySet) <=> exists(a, in(SetTheory.pair(a, t), emptySet)))) by InstantiateForall(emptySet)(
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
