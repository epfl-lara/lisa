import lisa.SetTheoryLibrary
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
import java.security.cert.Extension
import lisa.prooflib.BasicStepTactic.LeftExistsOne
import lisa.utils.Serialization.hypothesis
import lisa.prooflib.SimpleDeducedSteps.InstantiateForall
import scala.collection.immutable.ArraySeq
import scala.collection.immutable.HashMap
import lisa.utils.parsing.UnreachableException
import lisa.maths.settheory.types.TypeLib.{ |=>, given}
import lisa.maths.settheory.types.TypeSystem.{*, given}

object String extends lisa.Main {
  draft()

  val circ = ConstantFunctionLabel.infix("o", 2)

  def char(c: Char) =

    val zero = Constant("0")
    val one = Constant("1")
    val e = Constant("Ɛ")

    addSymbol(zero)
    addSymbol(one)
    addSymbol(circ)
    addSymbol(e)

    def toBinary(v: Int, b: Int = 8, buffer: Term = emptySet): Term =
      if b == 0 then buffer
      else toBinary(v >> 1, b - 1, circ(if v % 2 == 1 then one else zero, buffer))

    toBinary(c)

  def string(s: String) =
    // val stringTitle = variable
    // (DEF(stringTitle) --> s.foldRight(emptySet)((c, acc: Term) => circ(char(c), acc)))(Constant(s))
    s.foldRight(emptySet)((c, acc: Term) => circ(char(c), acc))

  val a = variable
  val b = variable
  val c = variable
  val d = variable

  val f = variable
  val g = variable

  val i = variable
  val j = variable
  val k = variable
  val l = variable

  val n = variable
  val n1 = variable
  val n2 = variable
  val m = variable

  val p = formulaVariable
  val p1 = formulaVariable
  val p2 = formulaVariable
  val p3 = formulaVariable
  val q = formulaVariable

  val r = variable
  val s = variable
  val t = variable

  val x = variable
  val y = variable
  val z = variable

  val A = variable
  val B = variable
  val S = variable

  val F = function[1]

  val P = predicate[1]
  val P2 = predicate[2]

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

  /**
   * One of the constructors of an algebraic data type.
   *
   * @tparam N arity of the constructor, i.e. the number of arguments it takes
   * @param adt name of the ADT
   * @param name name of the constructor
   * @param typeArgs types of the parameters of the constructor
   */
  class Constructor(using line: sourcecode.Line, file: sourcecode.File)(val name: String, val typeArgs: Seq[Type], val tag: Tag = null) {

    /**
     * Number of arguments in this constructor
     */
    val arity: Int = typeArgs.length

    /**
     * List of variables used in the definition of this constructor
     */
    val variables: Seq[Variable] = for i <- 0 until arity yield Variable(s"a${i}")

    val typeVariables: Seq[Variable] = 
      def termTypeVars(term: Term): Seq[Variable] = 
        term match
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

    //def term(args: Seq[Term]): Term = pair(nameTerm, subterm(args))
    def term(args: Seq[Term]): Term = pair(emptySet, subterm(args))

    val term: Term = term(variables)

    /**
     * @see [[this.term]]
     */
    def subterm(args: Seq[Term]): Term = args.foldRight(emptySet)((t, acc: Term) => pair(t, acc))

    // /**
    //  * Theorem --- Injectivity of constructors.
    //  *
    //  *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
    //  *
    //  * e.g. Cons(head1, tail1) === Cons(head2, tail2) <=> head1 === head1
    //  */
    // lazy val injectivityThm =
    //   label match
    //     case lb: Constant =>
    //       Theorem(lb === lb) {
    //         have(thesis) by Tautology
    //       }
    //     case lb: ConstantFunctionLabel[?] =>
    //       // variable sequences x_0, ..., x_n-1 and y_0, ..., y_n-1
    //       val xs = for i <- 0 until arity yield Variable(s"x${i}")
    //       val ys = for i <- 0 until arity yield Variable(s"y${i}")

    //       // this constructor instantiated with xs and ys
    //       val lxs = lb.applyUnsafe(xs)
    //       val lys = lb.applyUnsafe(ys)

    //       // internal representation of this constructor instantiated with xs ys
    //       val txs = term(xs)
    //       val tys = term(ys)

    //       // we first prove that lxs === lys <=> txs === tys
    //       // and then use pair extensionality (i.e. injectivity) to complete the proof
    //       Theorem((lxs === lys) <=> xs.zip(ys).map(_ === _).reduce(_ /\ _)) {

    //         val cons1def = have(lxs === txs) by Tautology.from(label.definition.of((variables.zip(xs).map((v, xvar) => v := xvar) :+ lxs): _*))
    //         val cons1defFlipped = thenHave(txs === lxs) by Tautology

    //         val cons2def = have(lys === tys) by Tautology.from(label.definition.of((variables.zip(ys).map((v, yvar) => v := yvar) :+ lys): _*))
    //         val cons2defFlipped = thenHave(tys === lys) by Tautology

    //         have(lxs === lys |- lxs === tys) by Tautology.from(cons2def, equalityTransitivity of (x := lxs, y := lys, z := tys))
    //         val imp1 = have(lxs === lys |- txs === tys) by Tautology.from(cons1defFlipped, lastStep, equalityTransitivity of (x := txs, y := lxs, z := tys))

    //         have(txs === tys |- lxs === tys) by Tautology.from(cons1def, equalityTransitivity of (x := lxs, y := txs, z := tys))
    //         val imp2 = have(txs === tys |- lxs === lys) by Tautology.from(lastStep, cons2defFlipped, equalityTransitivity of (x := lxs, y := tys, z := lys))

    //         have((lxs === lys) <=> (txs === tys)) by Tautology.from(imp1, imp2)

    //         // now chaining pair extentionality

    //         have((lxs === lys) <=> (subterm(xs) === subterm(ys))) by Tautology.from(lastStep, pairExtensionality of (a := nameTerm, b := subterm(xs), c := nameTerm, d := subterm(ys)))

    //         // list of the possible cuts of xs and ys without the first one (empty list, full list)
    //         val cumulX = xs.scanLeft[(List[Variable], List[Variable])]((Nil, xs.toList))((acc, _) => (acc._2.head :: acc._1, acc._2.tail)).tail
    //         val cumulY = xs.scanLeft[(List[Variable], List[Variable])]((Nil, ys.toList))((acc, _) => (acc._2.head :: acc._1, acc._2.tail)).tail

    //         for pl <- cumulX.zip(cumulY) do
    //           val left = pl._1._1.zip(pl._2._1).map(_ === _).reduce(_ /\ _)
    //           val rightX = subterm(pl._1._2)
    //           val rightY = subterm(pl._2._2)
    //           have((lxs === lys) <=> left /\ (rightX === rightY)) by Tautology.from(lastStep, pairExtensionality of (a := pl._1._1.head, b := rightX, c := pl._2._1.head, d := rightY))
    //       }

  }

  class TypedConstructor(using line: sourcecode.Line, file: sourcecode.File)(cons: Constructor, adt: ADT)  {

    val typeVariables = adt.typeVariables

    val typeArgs = cons.typeArgs.map{
      case Self => adt.term
      case BaseType(t) => t
    }
    val typ = typeArgs.foldRight[Term](adt.term)((a, b) => a |=> b)
    def app(c: Term)(s: Seq[Term]): Term = s.foldLeft(c)((acc, v) => acc*v)  


    val typedFunctionUniqueness = Lemma(existsOne(c, (c :: typ) /\ cons.variables.foldRight(app(c)(cons.variables) === cons.term)(forall(_, _)))) {
      sorry
    }

    val term = FunctionDefinition[0](s"${adt.name}/${cons.name}", line.value, file.value)(Seq(), c, (c :: typ) /\ cons.variables.foldRight(app(c)(cons.variables) === cons.term)(forall(_, _)), typedFunctionUniqueness).label

    val typeChecking = Theorem(term :: typ) {
      have((term === term) <=> (term :: typ) /\ cons.variables.foldRight(app(term)(cons.variables) === cons.term)(forall(_, _))) by InstantiateForall(term)(term.definition)
      thenHave(thesis) by Tautology
    }
  }

  // General purpose theorems

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

  // Helper: compute the union of the range of a functional
  def unionRange(f: Term) = union(relationRange(f))
  def restrRange(f: Term, n: Term) = relationRange(restrictedFunction(f, n))

  val unionEmpty = Lemma(union(emptySet) === emptySet) {
    sorry
  }

  val unionRangeMonotonic = Lemma(subset(f, g) |- subset(unionRange(f), unionRange(g))) {
    have(thesis) by Apply(unionMonotic).on(rangeMonotonic.asInstanceOf)
  }

  val restrictedFunctionEmptyDomain = Lemma(restrictedFunction(f, emptySet) === emptySet) {
    sorry
  }

  val unionRangeEmpty = Lemma(unionRange(emptySet) === emptySet) {
    have(!in(pair(a, t), emptySet)) by Exact(emptySetAxiom)
    thenHave(forall(a, !in(pair(a, t), emptySet))) by RightForall
    val s0 = thenHave(!exists(a, in(pair(a, t), emptySet))) by Restate

    have(!in(t, emptySet)) by Exact(emptySetAxiom)
    have(in(t, emptySet) <=> exists(a, in(pair(a, t), emptySet))) by Tautology.from(lastStep, s0)
    val defRHS = thenHave(forall(t, in(t, emptySet) <=> exists(a, in(pair(a, t), emptySet)))) by RightForall

    have((relationRange(emptySet) === emptySet) <=> forall(t, in(t, emptySet) <=> exists(a, in(pair(a, t), emptySet)))) by InstantiateForall(emptySet)(
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

  class ADT(using line: sourcecode.Line, file: sourcecode.File)(val name: String, val constructors: Seq[Constructor]) {

    println(s"Generating $name...")

    val before =  System.nanoTime

    val typeVariables = constructors.flatMap(_.typeVariables).distinct

    val constructorMap: Map[String, Constructor] = constructors.map(c => (c.name -> c)).toMap

    val exVar: Map[Constructor, Seq[Variable]] = constructors.map(c => (c -> (for i <- 0 until c.arity yield Variable(s"x${i}")))).toMap

    def consVarMembership(c: Constructor, vars: Seq[Term], s: Term): Formula = /\ (vars.zip(c.typeArgs).map((v, t) => in(v, getTermOrElse(t, s))))
    def consVarMembership(c: Constructor, s: Term): Formula = consVarMembership(c, c.variables, s)
    def consExVarMembership(c: Constructor, s: Term): Formula = consVarMembership(c, exVar(c), s)

    def isConstructor(c: Constructor, x: Term, s: Term): Formula = exVar(c).foldRight(consVarMembership(c, exVar(c), s) /\ (x === c.term(exVar(c))))((exv, f) => exists(exv, f))
    def isConstructor(x: Term, s: Term): Formula = \/ (constructors.map(c => isConstructor(c, x, s)))


    def getTermOrElse(t: Type, s: Term) = 
      t match {
        case Self => s
        case BaseType(te) => te
      } 

    //SMALL H

    def inSmallH(s: Term)(x: Term) = isConstructor(x, s) \/ in(x, s)

    val smallHMonotonic = Lemma(subset(s, t) |- inSmallH(s)(x) ==> inSmallH(t)(x)) {

      val subsetST = subset(s, t)

      have(subsetST |- forall(z, in(z, s) ==> in(z, t))) by Apply(equivalenceApply of (p1 := subsetST)).on(subsetAxiom.asInstanceOf)
      val subs = thenHave(subsetST |- in(z, s) ==> in(z, t)) by InstantiateForall(z)

      val subsetSeq = 
        for c <- constructors yield
          val labelWithExVar = c.term(exVar(c))
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

    val succInSmallH = constructorMap.map((k, c) => k -> Lemma(consVarMembership(c, s) |- inSmallH(s)(c.term)) {

        val andl = have(consVarMembership(c, s) |- consVarMembership(c, s)) by Hypothesis
        val andr = have(c.term === c.term) by Restate
        have(consVarMembership(c, s) |- consVarMembership(c, s) /\ (c.term === c.term)) by RightAnd(andl, andr)

        ((c.variables.zip(exVar(c))).foldRight((lastStep, c.variables, List[Variable]()))) ( (el, acc) => 

          val (va, v) = el
          val (_, accVa, accVb) = acc

          val varsLeft = accVa.init
          val varsRight = v :: accVb

          val vars = varsLeft ++ varsRight
          val rightSeq = accVb.foldRight(consVarMembership(c, vars, s) /\ (c.term(vars) === c.term))((exV, f) =>
            exists(exV, f)
          )

          (thenHave(consVarMembership(c, s) |- exists(v, rightSeq)) by RightExists, varsLeft, varsRight)
        )._1

        thenHave(consVarMembership(c, s) |- inSmallH(s)(c.term)) by Tautology
    })


    //BIG H
    def inBigH(f: Term)(x: Term) = !(f === emptySet) /\ inSmallH(unionRange(f))(x)

    val bigHMonotonic = Lemma(subset(f, g) |- inBigH(f)(x) ==> inBigH(g)(x)) {
      val s0l = have(subset(f, g) |- subset(unionRange(f), unionRange(g))) by Restate.from(unionRangeMonotonic)
      val s0r = have(subset(unionRange(f), unionRange(g)) |- inSmallH(unionRange(f))(x) ==> inSmallH(unionRange(g))(x)) by Restate.from(smallHMonotonic of (s := unionRange(f), t := unionRange(g)))
      have(subset(f, g) |- inSmallH(unionRange(f))(x) ==> inSmallH(unionRange(g))(x)) by Cut(s0l, s0r)
      val s1r = thenHave((subset(f, g), inBigH(f)(x)) |- inSmallH(unionRange(g))(x)) by Weakening

      val s1l = have((subset(f, g), inBigH(f)(x)) |- !(g === emptySet)) by Weakening(subsetNotEmpty of (x := f, y := g))
      have((subset(f, g), inBigH(f)(x)) |- inBigH(g)(x)) by RightAnd(s1l, s1r)
    }

    def gDef(g: Term) = functional(g) /\ (relationDomain(g) === N) /\ forall(b, in(b, N) ==> forall(x, in(x, app(g, b)) <=> inBigH(restrictedFunction(g, b))(x)))

    val gNotEmpty = Lemma(gDef(g) |- !(g === emptySet)) {
      val subst = have(gDef(g) |- relationDomain(g) === N) by Restate
      have((gDef(g), relationDomain(g) === emptySet, N === emptySet) |- ()) by Weakening(natNotEmpty)
      thenHave((gDef(g), relationDomain(g) === emptySet, emptySet === emptySet) |- ()) by Substitution.ApplyRules(subst)
      thenHave(gDef(g) |- !(relationDomain(g) === emptySet)) by Restate
      have(gDef(g) |- !(g === emptySet)) by Apply(emptyFunction).on(lastStep)
    }

    val inG = Lemma((gDef(g), in(n, N)) |- in(x, app(g, n)) <=> inBigH(restrictedFunction(g, n))(x)) {
      have(
        forall(b, in(b, N) ==> forall(x, in(x, app(g, b)) <=> inBigH(restrictedFunction(g, b))(x))) |- forall(b, in(b, N) ==> forall(x, in(x, app(g, b)) <=> inBigH(restrictedFunction(g, b))(x)))
      ) by Hypothesis
      thenHave(gDef(g) |- in(n, N) ==> forall(x, in(x, app(g, n)) <=> inBigH(restrictedFunction(g, n))(x))) by InstantiateForall(n)
      thenHave((gDef(g), in(n, N)) |- forall(x, in(x, app(g, n)) <=> inBigH(restrictedFunction(g, n))(x))) by Restate
      thenHave((gDef(g), in(n, N)) |- in(x, app(g, n)) <=> inBigH(restrictedFunction(g, n))(x)) by InstantiateForall(x)
    }

    // Lemma 1.3
    val cumulativeLemma = Lemma((gDef(g), in(n, N)) |- ∀(m, in(m, successor(n)) ==> subset(app(g, m), app(g, n)))) {
      have((gDef(g), in(n, N)) |- subset(m, n) <=> in(m, successor(n))) by Exact(natSubset)
      thenHave((gDef(g), in(n, N)) |- in(m, successor(n)) <=> subset(m, n)) by Restate
      val imp0 = have((gDef(g), in(n, N)) |- in(m, successor(n)) ==> subset(m, n)) by Apply(equivalenceApply).on(lastStep)

      have((gDef(g), in(n, N), subset(m, n)) |- in(x, app(g, m)) <=> inBigH(restrictedFunction(g, m))(x)) by Apply(inG).on(subsetIsNat.asInstanceOf)
      val eq1 = have((gDef(g), in(n, N), subset(m, n), in(x, app(g, m))) |- inBigH(restrictedFunction(g, m))(x)) by Apply(equivalenceRevApply of (p1 := in(x, app(g, m)))).on(lastStep)

      have(subset(m, n) |- inBigH(restrictedFunction(g, m))(x) ==> inBigH(restrictedFunction(g, n))(x)) by Apply(bigHMonotonic).on(restrictedFunctionDomainMonotonic.asInstanceOf)
      have((gDef(g), in(n, N), subset(m, n), inBigH(restrictedFunction(g, m))(x)) |- in(x, app(g, n))) by Apply(equivalenceRevApply).on(lastStep, inG.asInstanceOf)
      have((gDef(g), in(n, N), subset(m, n), in(x, app(g, m))) |- in(x, app(g, n))) by Cut(eq1, lastStep)
      thenHave((gDef(g), in(n, N), subset(m, n)) |- in(x, app(g, m)) ==> in(x, app(g, n))) by Restate
      thenHave((gDef(g), in(n, N), subset(m, n)) |- forall(x, in(x, app(g, m)) ==> in(x, app(g, n)))) by RightForall
      have((gDef(g), in(n, N), subset(m, n)) |- subset(app(g, m), app(g, n))) by Apply(equivalenceRevApply).on(lastStep, subsetAxiom.asInstanceOf)
      have((gDef(g), in(n, N)) |- in(m, successor(n)) ==> subset(app(g, m), app(g, n))) by Apply(lastStep).on(imp0)
      thenHave(thesis) by RightForall
    }

    val adtLevelZeroLemma = Lemma(gDef(g) |- !in(x, app(g, emptySet))) {
      have(gDef(g) |- in(x, app(g, emptySet)) <=> inBigH(restrictedFunction(g, emptySet))(x)) by Apply(inG).on(zeroIsNat.asInstanceOf)
      thenHave(gDef(g) |- in(x, app(g, emptySet)) <=> inBigH(emptySet)(x)) by Substitution.ApplyRules(restrictedFunctionEmptyDomain)
    }


    val inGSucc = Lemma((gDef(g), in(n, N)) |- in(x, app(g, successor(n))) <=> inSmallH(app(g, n))(x)) {
      val restrFunNotEmpty = have(gDef(g) |- !(restrictedFunction(g, successor(n)) === emptySet)) by Apply(restrictedFunctionNotEmpty).on(gNotEmpty.asInstanceOf, zeroIsNotSucc.asInstanceOf)
      
      val unionRangeSubst = have((gDef(g), in(n, N)) |- unionRange(restrictedFunction(g, successor(n))) === app(g, n)) by Apply(unionRangeLemma).on(cumulativeLemma.asInstanceOf)
      have((gDef(g), in(n, N)) |- in(x, app(g, successor(n))) <=> inBigH(restrictedFunction(g, successor(n)))(x)) by Apply(inG).on(equivalenceApply of (p1 := in(n, N)), successorIsNat.asInstanceOf)
      thenHave((gDef(g), in(n, N)) |- in(x, app(g, successor(n))) <=> !(restrictedFunction(g, successor(n)) === emptySet) /\ inSmallH(app(g, n))(x)) by Substitution.ApplyRules(unionRangeSubst)
      have(thesis) by Tautology.from(lastStep, restrFunNotEmpty)
    }

    val gExistence = Lemma(exists(g, gDef(g))) {
      sorry
    }

    val gUniqueness = Lemma(existsOne(g, gDef(g))) {
      sorry
    }

    def termDefinition(z: Term): Formula = forall(t, in(t, z) <=> forall(g, gDef(g) ==> in(t, unionRange(g))))

    val termExistence = Lemma(existsOne(z, termDefinition(z))) {
      have(exists(z, forall(t, in(t, z) <=> forall(g, gDef(g) ==> in(t, unionRange(g)))))) subproof {
        sorry
      }
      have(thesis) by Apply(uniqueByExtension of (schemPred := lambda(t, forall(g, gDef(g) ==> in(t, unionRange(g)))))).on(lastStep)
    }

  
    val term = FunctionDefinition[0](name, line.value, file.value)(Seq(), z, forall(t, in(t, z) <=> forall(g, gDef(g) ==> in(t, unionRange(g)))), termExistence).label


    val inTerm = Lemma(gDef(g) |- in(x, term) <=> in(x, unionRange(g))) {
      have((term === term) <=> termDefinition(term)) by InstantiateForall(term)(term.definition)
      thenHave(termDefinition(term)) by Tautology
      val termDef = thenHave(in(x, term) <=> forall(g, gDef(g) ==> in(x, unionRange(g)))) by InstantiateForall(x)
      val termDefL = have(in(x, term) |- forall(g, gDef(g) ==> in(x, unionRange(g)))) by Apply(equivalenceApply).on(termDef)
      val termDefR = have(forall(g, gDef(g) ==> in(x, unionRange(g))) |- in(x, term)) by Apply(equivalenceRevApply).on(termDef)


      have(forall(g, gDef(g) ==> in(x, unionRange(g))) |- forall(g, gDef(g) ==> in(x, unionRange(g)))) by Hypothesis
      thenHave(forall(g, gDef(g) ==> in(x, unionRange(g))) |- gDef(g) ==> in(x, unionRange(g))) by InstantiateForall(g)
      thenHave((forall(g, gDef(g) ==> in(x, unionRange(g))), gDef(g)) |- in(x, unionRange(g))) by Restate

      val caseL = have((gDef(g), in(x, term)) |- in(x, unionRange(g))) by Apply(lastStep).on(termDefL)

      //have((gDef(g), in(x, unionRange(g), gDef(f) /\ !in(x, unionRange()))))) |- in(x, unionRange(g))) by Hypothesis
      //thenHave()

      sorry

    }

    val adtHasAnHeightLemma = Lemma(gDef(g) |- (in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(g, n))))) {
      val substDomain = have((relationDomain(g) === N) |- (relationDomain(g) === N)) by Hypothesis
      have((in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> (in(n, relationDomain(g)) /\ in(x, app(g, n)))) by Exact(equivalenceReflexivity)
      thenHave(gDef(g) |- (in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> (in(n, N) /\ in(x, app(g, n)))) by Substitution.ApplyRules(substDomain)
      thenHave(gDef(g) |- forall(n, (in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> (in(n, N) /\ in(x, app(g, n))))) by RightForall
      val rew = have(gDef(g) |- exists(n, in(n, relationDomain(g)) /\ in(x, app(g, n))) <=> exists(n, in(n, N) /\ in(x, app(g, n)))) by Apply(
        existentialEquivalenceDistribution of (P := lambda(n, in(n, relationDomain(g)) /\ in(x, app(g, n))), Q := lambda(n, in(n, N) /\ in(x, app(g, n))))
      ).on(lastStep)

      have(gDef(g) |- (in(x, term) <=> ∃(n, in(n, relationDomain(g)) /\ in(x, app(g, n))))) by Apply(equivalenceRewriting).on(unionRangeMembership.asInstanceOf, inTerm.asInstanceOf)
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, rew)
    }

    val adtHasAnHeightGenLemma = constructorMap.map((k, c) => k -> Lemma(gDef(g) |- (consVarMembership(c, term) <=> ∃(n, in(n, N) /\ consVarMembership(c, app(g, n))))) {
      
      val imp0 = have((gDef(g), ∃(n, in(n, N) /\ consVarMembership(c, app(g, n)))) |- consVarMembership(c, term)) subproof {
        val andSeq = for((v, ty) <- c.variables.zip(c.typeArgs)) yield
          ty match
            case Self => 
              have((gDef(g), in(n, N) /\ in(v, app(g, n))) |- in(n, N) /\ in(v, app(g, n))) by Restate
              thenHave((gDef(g), in(n, N) /\ in(v, app(g, n))) |- exists(n, in(n, N) /\ in(v, app(g, n)))) by RightExists
              have((gDef(g), in(n, N) /\ in(v, app(g, n))) |- in(v, term)) by Apply(equivalenceRevApply).on(lastStep, adtHasAnHeightLemma.asInstanceOf)
            case BaseType(t) =>
              have((gDef(g), in(n, N) /\ in(v, t)) |- in(v, t)) by Restate
          thenHave((gDef(g), in(n, N) /\ consVarMembership(c, app(g, n))) |- in(v, getTermOrElse(ty, term))) by Weakening
          
        have((gDef(g), in(n, N) /\ consVarMembership(c, app(g, n))) |- consVarMembership(c, term)) by AndAggregate(andSeq)
        thenHave((gDef(g), exists(n, in(n, N) /\ consVarMembership(c, app(g, n)))) |- consVarMembership(c, term)) by LeftExists
      }

      val imp1 = have((gDef(g), consVarMembership(c, term)) |- ∃(n, in(n, N) /\ consVarMembership(c, app(g, n)))) subproof {
        sorry
      }

      have(thesis) by Tautology.from(imp0, imp1)
    })

    val adtSuccessorLemma = constructorMap.map((k, c) => k -> Lemma((gDef(g), in(n, N)) |- consVarMembership(c, app(g, n)) ==> in(c.term, app(g, successor(n)))) {
      
      val s0 = have(consVarMembership(c, app(g, n)) |- inSmallH(app(g, n))(c.term)) by Restate.from(succInSmallH(k) of (s := app(g, n)))
      val s1 = have((gDef(g), in(n, N)) |- in(c.term, app(g, successor(n))) <=> inSmallH(app(g, n))(c.term)) by Exact(inGSucc)
      
      have((gDef(g), in(n, N), inSmallH(app(g, n))(c.term),  in(c.term, app(g, successor(n))) <=> inSmallH(app(g, n))(c.term)) |- in(c.term, app(g, successor(n)))) by Exact(equivalenceRevApply)
      have((gDef(g), in(n, N), inSmallH(app(g, n))(c.term)) |- in(c.term, app(g, successor(n)))) by Cut(s1, lastStep)
      have((gDef(g), in(n, N), consVarMembership(c, app(g, n))) |- in(c.term, app(g, successor(n)))) by Cut(s0, lastStep)
    })

    val adtTypechecking = constructorMap.map((k, c) => { k ->
      Lemma(removeConstants(consVarMembership(c, term) ==> in(c.term, term))) {
    
      val succNIsTerm = have((gDef(g), in(n, N), in(c.term, app(g, successor(n)))) |- in(c.term, term)) subproof {
        have(in(n, N) |- in(successor(n), N)) by Apply(equivalenceApply).on(successorIsNat.asInstanceOf)
        val s0l = thenHave((gDef(g), in(n, N), in(c.term, app(g, successor(n)))) |- in(successor(n), N)) by Weakening

        val s0r = have((gDef(g), in(n, N), in(c.term, app(g, successor(n)))) |- in(c.term, app(g, successor(n)))) by Restate
        have((gDef(g), in(n, N), in(c.term, app(g, successor(n)))) |- in(successor(n), N) /\ in(c.term, app(g, successor(n)))) by RightAnd(s0l, s0r)
        thenHave((gDef(g), in(n, N), in(c.term, app(g, successor(n)))) |- exists(m, in(m, N) /\ in(c.term, app(g, m)))) by RightExists
        have((gDef(g), in(n, N), in(c.term, app(g, successor(n)))) |- in(c.term, term)) by Apply(equivalenceRevApply).on(lastStep, adtHasAnHeightLemma.asInstanceOf)
      }

      have((gDef(g), in(n, N), consVarMembership(c, app(g, n))) |- in(c.term, app(g, successor(n)))) by Restate.from(adtSuccessorLemma(k))
      have((gDef(g), in(n, N), consVarMembership(c, app(g, n))) |- in(c.term, term)) by Cut(lastStep, succNIsTerm)
      thenHave((gDef(g), in(n, N) /\ consVarMembership(c, app(g, n))) |- in(c.term, term)) by Restate
      val s1 = thenHave((gDef(g), exists(n, in(n, N) /\ consVarMembership(c, app(g, n)))) |- in(c.term, term)) by LeftExists
      have((gDef(g), consVarMembership(c, term)) |- exists(n, in(n, N) /\ consVarMembership(c, app(g, n)))) by Apply(equivalenceApply).on(adtHasAnHeightGenLemma(k).asInstanceOf)
      have((gDef(g), consVarMembership(c, term)) |- in(c.term, term)) by Cut(lastStep, s1)
      thenHave(gDef(g) |- consVarMembership(c, term) ==> in(c.term, term)) by Restate
      thenHave(exists(g, gDef(g)) |- consVarMembership(c, term) ==> in(c.term, term)) by LeftExists
      have(consVarMembership(c, term) ==> in(c.term, term)) by Cut(gExistence, lastStep)
      thenHave(thesis) by Restate
    }
  })

    
    lazy val succInG = Lemma((gDef(g), in(n, N)) |- in(x, app(g, successor(n))) <=> isConstructor(x, app(g, n))) {

      val impl = have((gDef(g), in(n, N), inSmallH(app(g, n))(x)) |- isConstructor(x, app(g, n))) subproof {
        
        def prop(n: Term) = inSmallH(app(g, n))(x) ==> isConstructor(x, app(g, n))
        
        have(inSmallH(app(g, emptySet))(x) |- isConstructor(x, app(g, emptySet)) \/ in(x, app(g, emptySet))) by Hypothesis
        val baseCase = have(gDef(g) |- prop(emptySet)) by Tautology.from(lastStep, adtLevelZeroLemma)
      
        val indThm = have((gDef(g), prop(emptySet)) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Exact(natInduction of (P := lambda(k, prop(k))))
        val indPart0 = have(gDef(g) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Cut(baseCase, indThm)
        
        val succInN = have(in(m, N) |- in(successor(m), N)) by Apply(equivalenceApply of (p1 := in(m, N))).on(successorIsNat.asInstanceOf)
        val succSuccInN = have(in(m, N) |- in(successor(successor(m)), N)) by Apply(equivalenceApply).on(succInN, successorIsNat.asInstanceOf)
        have(in(m, N) |- in(successor(m), successor(successor(m)))) by Apply(inSuccessor).on(succInN)
        val inSuccSucc = have(in(m, N) |- in(m, successor(successor(m)))) by Apply(natTransitive).on(lastStep, succSuccInN, inSuccessor.asInstanceOf)

        have((gDef(g), in(m, N)) |- forall(k, in(k, successor(successor(m))) ==> subset(app(g, k), app(g, successor(m))))) by Apply(cumulativeLemma).on(succInN)
        thenHave((gDef(g), in(m, N)) |- in(m, successor(successor(m))) ==> subset(app(g, m), app(g, successor(m)))) by InstantiateForall(m)
        have((gDef(g), in(m, N)) |- subset(app(g, m), app(g, successor(m)))) by Apply(lastStep).on(inSuccSucc)
        have((gDef(g), in(m, N)) |- forall(x, in(x, app(g, m)) ==> in(x, app(g, successor(m))))) by Apply(equivalenceApply).on(lastStep, subsetAxiom)
        val escalate0 = thenHave((gDef(g), in(m, N)) |- in(y, app(g, m)) ==> in(y, app(g, successor(m)))) by InstantiateForall(y)

        
        val orSeq = 
          for c <- constructors yield
            val labelWithExVar = c.term(exVar(c))

            val andSeq0 = 
              for (v, ty) <- exVar(c).zip(c.typeArgs) yield
                have((gDef(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- in(v, getTermOrElse(ty, app(g, successor(m))))) by Weakening(escalate0 of (y := v))

            val s0l = have((gDef(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- consExVarMembership(c, app(g, successor(m)))) by AndAggregate(andSeq0)
            val s0r = have((gDef(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- labelWithExVar === x) by Restate

            have((gDef(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- consExVarMembership(c, app(g, successor(m))) /\ (labelWithExVar === x)) by RightAnd(s0l, s0r)

            exVar(c).foldRight(lastStep) ( (v, acc) => 
                thenHave((gDef(g), in(m, N), consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x)) |- exists(v, acc.statement.right.head)) by RightExists
              )
            
            (exVar(c).foldRight((lastStep, consExVarMembership(c, app(g, m)) /\ (labelWithExVar === x))) ( (v, acc) => 
                val (accFact, accSeq) = acc
                (thenHave((gDef(g), in(m, N), exists(v, accSeq)) |- isConstructor(c, x, app(g, successor(m)))) by LeftExists, exists(v, accSeq))
              ))._1

            thenHave((gDef(g), in(m, N), isConstructor(c, x, app(g, m))) |- isConstructor(x, app(g, successor(m)))) by Weakening
        

        
        val escalate1 = have((gDef(g), in(m, N), isConstructor(x, app(g, m))) |- isConstructor(x, app(g, successor(m)))) by OrAggregate(orSeq)


        val s0 = have((gDef(g), in(m, N), in(x, app(g, successor(m)))) |- inSmallH(app(g, m))(x)) by Apply(equivalenceApply of (p1 := in(x, app(g, successor(m))))).on(inGSucc.asInstanceOf)
        have(prop(m) |- prop(m)) by Hypothesis
        have((gDef(g), in(m, N), in(x, app(g, successor(m))), prop(m)) |- isConstructor(x, app(g, m))) by Apply(lastStep).on(s0)
        have((gDef(g), in(m, N), in(x, app(g, successor(m))), prop(m)) |- isConstructor(x, app(g, successor(m)))) by Cut(lastStep, escalate1)


        thenHave((gDef(g), in(m, N), prop(m), inSmallH(app(g, successor(m)))(x)) |- isConstructor(x, app(g, successor(m)))) by Tautology
        thenHave((gDef(g), in(m, N), prop(m)) |- prop(successor(m))) by Restate
        thenHave(gDef(g) |- in(m, N) ==> (prop(m) ==> prop(successor(m)))) by Restate
        thenHave(gDef(g) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m))))) by RightForall
        have(gDef(g) |- forall(n, in(n, N) ==> prop(n))) by Apply(indPart0).on(lastStep)
        thenHave(gDef(g) |- in(n, N) ==> prop(n)) by InstantiateForall(n)
        thenHave(thesis) by Restate
      }
      val impr = have((gDef(g), in(n, N)) |- isConstructor(x, app(g, n)) ==> inSmallH(app(g, n))(x)) subproof {
        have(thesis) by Tautology
      }

      have((gDef(g), in(n, N)) |- inSmallH(app(g, n))(x) <=> isConstructor(x, app(g, n))) by Tautology.from(impl, impr)
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, inGSucc.asInstanceOf)
    }

    def structuralInductionPrecond(c: Constructor): Formula =
      exVar(c).zip(c.typeArgs).foldRight[Formula](P(c.term(exVar(c)))) ( (el, fc) =>
          val (v, ty) = el
          ty match
            case Self => forall(v, in(v, term) ==> (P(v) ==> fc))
            case BaseType(t) => forall(v, in(v, t) ==> fc)
        )

    val structuralInduction = THM(constructors.foldRight[Formula](forall(x, in(x, term) ==> P(x)))( (c, f) => structuralInductionPrecond(c) ==> f), s"${name} structural induction", line.value, file.value, Theorem)  {

      val preconditions = /\ (constructors.map(structuralInductionPrecond))
            
      def prop(n: Term) = forall(x, in(x, app(g, n)) ==> P(x)) 

      val baseCase = have(gDef(g) |- prop(emptySet)) subproof {
        have(gDef(g) |- in(x, app(g, emptySet)) ==> P(x)) by Weakening(adtLevelZeroLemma)
        thenHave(thesis) by RightForall
      }

      val inductionThm = have((gDef(g), prop(emptySet)) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Exact(natInduction of (P := lambda(k, prop(k))))
      val indPart0 = have(gDef(g) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m)))) ==> forall(n, in(n, N) ==> prop(n))) by Cut(baseCase, inductionThm)
      
      val inductiveCase = have((gDef(g), preconditions) |- forall(m, in(m, N) ==> (prop(m) ==> prop(successor(m))))) subproof {
        val orSeq = 
          (for (k, c) <- constructorMap yield

            val precond = structuralInductionPrecond(c)
            val labelWithExVar = c.term(exVar(c))
            val consExVarMembershipAppGM = consExVarMembership(c, app(g, m))
            val consExVarMembershipAppGMEx = ∃(m, in(m, N) /\ consExVarMembership(c, app(g, m)))
            val consExVarMembershipTerm = consExVarMembership(c, term)

            val consExVarMembershipAppGMToTerm = have((gDef(g), in(m, N), consExVarMembershipAppGM) |- consExVarMembershipTerm) subproof {
              have((gDef(g), in(m, N), consExVarMembershipAppGM) |- in(m, N) /\ consExVarMembershipAppGM) by Restate
              val consVarL = thenHave((gDef(g), in(m, N), consExVarMembershipAppGM) |- consExVarMembershipAppGMEx) by RightExists
              val s0 = have(gDef(g) |- consExVarMembershipTerm <=> consExVarMembershipAppGMEx) by Restate.from(adtHasAnHeightGenLemma(k).of(c.variables.zip(exVar(c)).map(_ := _) : _*))
              have((consExVarMembershipTerm <=> consExVarMembershipAppGMEx, consExVarMembershipAppGMEx) |- consExVarMembershipTerm) by Restate.from(equivalenceRevApply of (p1 := consExVarMembershipTerm, p2 := consExVarMembershipAppGMEx))
              val consVarR = have((gDef(g), consExVarMembershipAppGMEx) |- consExVarMembershipTerm) by Cut(s0, lastStep)
              have(thesis) by Cut(consVarL, consVarR)
            }

            have((gDef(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- precond) by Restate


            exVar(c).zip(c.typeArgs).foldLeft(lastStep)( (fact, el) =>
              val ccl = fact.statement.right.head
              val (v, ty) = el

              ccl match
                case Forall(_, phi) => 
                  val instantiation = thenHave((gDef(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- phi) by InstantiateForall(v)
                  
                  phi match 
                    case Implies(membership, psi) => 
                      ty match
                        case Self => 
                          psi match
                            case Implies(_, theta) => 
                              have(prop(m) |- prop(m)) by Hypothesis
                              thenHave(prop(m) |- in(v, app(g, m)) ==> P(v)) by InstantiateForall(v)
                              val pv = thenHave((prop(m), consExVarMembershipAppGM) |- P(v)) by Weakening

                              have((gDef(g), precond, in(m, N), prop(m), consExVarMembershipTerm, consExVarMembershipAppGM, P(v)) |- theta) by Weakening(instantiation)
                              have((gDef(g), precond, in(m, N), prop(m), consExVarMembershipTerm, consExVarMembershipAppGM) |- theta) by Cut(pv, lastStep)
                              have((gDef(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- theta) by Cut(consExVarMembershipAppGMToTerm, lastStep)
                              
                            case _ => throw UnreachableException

                        case BaseType(t) =>
                          thenHave((gDef(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- psi) by Restate
                    case _ => throw UnreachableException
                case _ => throw UnreachableException
            )

            val substL = thenHave((gDef(g), precond, in(m, N), prop(m), consExVarMembershipAppGM) |- P(labelWithExVar)) by Restate
            val substR = have((labelWithExVar === x, P(labelWithExVar)) |- P(x)) by Restate.from(substitutionThm of (x := labelWithExVar, y := x))
            have((gDef(g), precond, in(m, N), prop(m), consExVarMembershipAppGM, labelWithExVar === x) |- P(x)) by Cut(substL, substR)

            thenHave((gDef(g), precond, in(m, N), prop(m), consExVarMembershipAppGM /\ (labelWithExVar === x)) |- P(x)) by Restate

            (exVar(c).foldRight((lastStep, consExVarMembershipAppGM /\ (labelWithExVar === x))) ( (v, acc) => 
              val (accFact, accSeq) = acc
              (thenHave((gDef(g), precond, in(m, N), prop(m), exists(v, accSeq)) |- P(x)) by LeftExists, exists(v, accSeq))
            ))._1

            thenHave((gDef(g), preconditions, in(m, N), prop(m), isConstructor(c, x, app(g, m))) |- P(x)) by Weakening).toSeq

        val appsucc = have((gDef(g), in(m, N), in(x, app(g, successor(m)))) |- isConstructor(x, app(g, m))) by Apply(equivalenceApply).on(succInG.asInstanceOf)

        have((gDef(g), preconditions, in(m, N), prop(m), isConstructor(x, app(g, m))) |- P(x)) by OrAggregate(orSeq)
        have((gDef(g), preconditions, in(m, N), prop(m), in(x, app(g, successor(m)))) |- P(x)) by Apply(lastStep).on(appsucc)
        thenHave((gDef(g), preconditions, in(m, N), prop(m)) |- in(x, app(g, successor(m))) ==> P(x)) by Restate


        have((gDef(g), preconditions, in(m, N), prop(m), in(x, app(g, successor(m)))) |- P(x)) by Apply(lastStep).on(appsucc)
        thenHave((gDef(g), preconditions, in(m, N), prop(m)) |- in(x, app(g, successor(m))) ==> P(x)) by Restate

        thenHave((gDef(g), preconditions, in(m, N), prop(m)) |- prop(successor(m))) by RightForall
        thenHave((gDef(g), preconditions) |- in(m, N) ==> (prop(m) ==> prop(successor(m)))) by Restate
        thenHave(thesis) by RightForall
      }


      have((gDef(g), preconditions) |- forall(n, in(n, N) ==> prop(n))) by Apply(indPart0).on(lastStep)
      thenHave((gDef(g), preconditions) |- in(n, N) ==> prop(n)) by InstantiateForall(n)
      thenHave((gDef(g), preconditions, in(n, N)) |- prop(n)) by Restate
      thenHave((gDef(g), preconditions, in(n, N)) |- in(x, app(g, n)) ==> P(x)) by InstantiateForall(x)
      thenHave((gDef(g), preconditions, in(n, N) /\ in(x, app(g, n))) |- P(x)) by Restate
      val exImpliesP = thenHave((gDef(g), preconditions, exists(n, in(n, N) /\ in(x, app(g, n)))) |- P(x)) by LeftExists
      have((gDef(g), in(x, term)) |- exists(n, in(n, N) /\ in(x, app(g, n)))) by Apply(equivalenceApply of (p1 := in(x, term))).on(adtHasAnHeightLemma.asInstanceOf)

      have((gDef(g), preconditions, in(x, term)) |- P(x)) by Cut(lastStep, exImpliesP)
      thenHave((exists(g, gDef(g)), preconditions, in(x, term)) |- P(x)) by LeftExists
      have(preconditions |- in(x, term) ==> P(x)) by Apply(lastStep).on(gExistence.asInstanceOf)
      thenHave(preconditions |- forall(x, in(x, term) ==> P(x))) by RightForall
      thenHave(thesis) by Restate
    }

    show(structuralInduction)

    // // // Theorem 2.1
    val patternMatchingThm = THM(in(x, term) |- removeConstants(isConstructor(x, term)), s"${name} pattern constructors", line.value, file.value, Theorem) {

      def ineqPrecond(c: Constructor): Formula =
        exVar(c).zip(c.typeArgs).foldRight[Formula](!(x === c.term(exVar(c)))) ( (el, fc) =>
            val (v, ty) = el
            ty match
              case Self => forall(v, in(v, term) ==> (!(x === v) ==> fc))
              case BaseType(t) => forall(v, in(v, t) ==> fc)
        )

      val preconditions = /\ (constructors.map(ineqPrecond))


      def negIneqPrecond(c: Constructor): Formula =
        exVar(c).zip(c.typeArgs).foldRight[Formula](x === c.term(exVar(c))) ( (el, fc) =>
            val (v, ty) = el
            ty match
              case Self => exists(v, in(v, term) /\ (!(x === v) /\ fc))
              case BaseType(t) => exists(v, in(v, t) /\ fc)
        )

      val negPreconditions = \/ (constructors.map(negIneqPrecond))

      def negWeakIneqPrecond(c: Constructor): Formula =
        exVar(c).zip(c.typeArgs).foldRight[Formula](c.term(exVar(c)) === x) ( (el, fc) =>
            val (v, ty) = el
            exists(v, in(v, getTermOrElse(ty, term)) /\ fc)
        )

      val orSeq = 
        for c <- constructors yield
          val s0l = have(negIneqPrecond(c) |- negWeakIneqPrecond(c)) subproof {
            have(x === c.term(exVar(c)) |- c.term(exVar(c)) === x) by Restate

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

              val weakr = thenHave(in(v, getTermOrElse(ty, term)) /\ left |- right) by Weakening
              val weakl = have(in(v, getTermOrElse(ty, term)) /\ left |- in(v, getTermOrElse(ty, term))) by Restate

              have(in(v, getTermOrElse(ty, term)) /\ left |- in(v, getTermOrElse(ty, term)) /\ right) by RightAnd(weakl, weakr)
              thenHave(in(v, getTermOrElse(ty, term)) /\ left |- exists(v, in(v, getTermOrElse(ty, term)) /\ right)) by RightExists
              thenHave(exists(v, in(v, getTermOrElse(ty, term)) /\ left) |- exists(v, in(v, getTermOrElse(ty, term)) /\ right)) by LeftExists
            )

          }
          val s0r = have(negWeakIneqPrecond(c) |- isConstructor(c, x, term)) by Tableau
          have(negIneqPrecond(c) |- isConstructor(c, x, term)) by Cut(s0l, s0r)
          thenHave(negIneqPrecond(c) |- isConstructor(x, term)) by Weakening
      
      val weaken = have(negPreconditions |- isConstructor(x, term)) by OrAggregate(orSeq)

      have(preconditions |- forall(z, in(z, term) ==> !(x === z))) by Exact(structuralInduction of (P := lambda(z, !(x === z))))
      thenHave(preconditions |- in(x, term) ==> !(x === x)) by InstantiateForall(x)
      val ind = thenHave(preconditions |- !in(x, term)) by Restate
      thenHave(!negPreconditions |- !in(x, term)) by Restate
      thenHave(in(x, term) |- negPreconditions) by Restate


      

      have(in(x, term) |- isConstructor(x, term)) by Cut(lastStep, weaken)
      thenHave(thesis) by Restate
    }

    show(patternMatchingThm)

  
    val totalTime = (System.nanoTime - before) / 1000000
    println(s"Total time: $totalTime ms")
  }


 

  //ADT("nat", Seq(Constructor[0]("nat", "base1", Seq()), Constructor[1]("nat", "cons", Seq(Self))))
  //ADT("nat", Seq(Constructor[0]("nat", "base1", Seq()), Constructor[0]("nat", "base2", Seq()), Constructor[1]("nat", "param", Seq(BaseType(emptySet))), Constructor[2]("nat", "cons", Seq(BaseType(emptySet), Self))))
  //ADT("tree", Seq(Constructor[0]("tree", "redLeaf", Seq()), Constructor[0]("tree", "blackLeaf", Seq()), Constructor[1]("tree", "paramLeaf", Seq(BaseType(T))), Constructor[1]("tree", "oneNode", Seq(Self)), Constructor[2]("tree", "twoNode", Seq(Self, Self)), Constructor[4]("tree", "fourNode", Seq(BaseType(singleton(emptySet)), Self, BaseType(singleton(emptySet)), Self))))

  def AllGood = Theorem(True) {
    have(thesis) by Tautology
  }
  
  protected trait ConstructorConverter[T] {
    def apply(t: T): ConstructorBuilder
  }

  given unit_to_cons: ConstructorConverter[Unit] with {
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

  

  given type_to_const: ConstructorConverter[Type] with {
    override def apply(t: Type): ConstructorBuilder = ConstructorBuilder(t)
  }

  given adt_to_const: ConstructorConverter[ADT] with {
    override def apply(a: ADT): ConstructorBuilder = ConstructorBuilder(Self)
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
    infix def | (b: ADTBuilder): ADTBuilder = ADTBuilder(this +: b.cons )
    infix def ++ (b: ConstructorBuilder): ConstructorBuilder = ConstructorBuilder((param.toSeq ++ b.param.toSeq): _*)
  }

  case class ADTBuilder(cons: Seq[ConstructorBuilder]) {
    infix def | (b: ADTBuilder): ADTBuilder = ADTBuilder(cons ++ b.cons)
    infix def | (b: ConstructorBuilder): ADTBuilder = ADTBuilder(cons :+ b)
    infix def | (u: Unit): ADTBuilder = this | any_to_const(u)
    infix def | (t: Type): ADTBuilder = this | any_to_const(t)
    infix def | (s: Seq[Type]): ADTBuilder = this | any_to_const(s)
    infix def | (t: EmptyTuple): ADTBuilder = this | any_to_const(t)
    infix def | [T <: Tuple](t: Type *: T)(using c: ConstructorConverter[T]): ADTBuilder = this | (any_to_const(t.head) ++ any_to_const(t.tail))

  }

  case class constructors(c: Constructor *)

  object constructors {
    def apply(c: Constructor*): constructors = new constructors(c: _*)
    def apply(adt: ADT)(cases: Case*): Term = ???
  }

  // object matches {
  //   def unapplySeq[N <: Arity](using name: sourcecode.FullName)(c: ADTBuilder): Option[Seq[Constructor]] = 
  //     Some(c.cons.zipWithIndex.map((c, i) => Constructor(name.value, s"Constructor$i", c.param)))
  // }

  object define {
    def unapply(using name: sourcecode.FullName)(c: ADTBuilder): (ADT, constructors) = 
      val constr = c.cons.zipWithIndex.map((c, i) => Constructor(s"Constructor$i", c.param, s"$i")) 
      (ADT(name.value, constr), constructors(constr: _*))
  }


  val cT = Constant("T")
  addSymbol(cT)

  val T = BaseType(cT)

  object Case {
    def apply(c: Constructor)(f: (Seq[Variable], Term)): Case = new Case(c)(f)
    def apply(c: Constructor)(f: => Term): Case = new Case(c)((Seq.empty, f))
  }

  case class Case(c: Constructor)(f: (Seq[Variable], Term)) {
    //def apply(args: Term *): Term = f(args: _*)
  }














  val define(list: ADT, constructors(nil, cons)) = () | (T, list)
  //val define(tree: ADT, constructors(leaf, node)) = emptySet | (tree, tree)

  // val mirror: Term = constructors(tree) (
  //   Case(leaf){
  //     leaf()
  //   }, 
  //   Case(node) {
  //     (l, r) -> node(app(mirror, r), app(mirror, l))
  //   }
  // )















  
  // val ADT(list, matches(nil, cons)) = () | (T, Self)

  

  //(nat, zero, succ) = ADT of (() | (T, self))

  val adt = ADT("Nat", Seq(Constructor("Zero", Seq()), Constructor("Succ", Seq(Self))))
  val tzero = TypedConstructor(adt.constructorMap("Zero"), adt)
  val tsucc = TypedConstructor(adt.constructorMap("Succ"), adt)
  // // println(tzero.typeChecking.statement)
  // // println(tsucc.typeChecking.statement)

  // AllGood
  // ADT("List", Seq(Constructor("List", "Nil", Seq()), Constructor("List", "Cons", Seq(T, Self))))
  // AllGood
  // ADT("Tree", Seq(Constructor("Tree", "Leaf", Seq()), Constructor("Tree", "Node", Seq(Self, Self))))
  // AllGood
    

  

}
