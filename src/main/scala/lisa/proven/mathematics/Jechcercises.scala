package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.proven.mathematics.SetTheory
import lisa.proven.mathematics.SetTheory2.*
import lisa.utils.Printer

/**
 * Practicing exercises from Jech, some of them may be moved to become theorems
 */
object Jechcercises extends lisa.proven.mathematics.BasicDefs {

  // var defs
  val x = variable
  val y = variable
  val z = variable
  val t = variable
  val a = variable
  val b = variable
  val c = variable
  val d = variable

  val P = predicate(1)
  val Q = predicate(1)

  // exercise 1.1

  val unorderedPairExtensionality = makeTHM(
    () |- (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))
  ) {
    // forward direction
    //      up ab = up cd |- a = c and b = d OR a = d and b = c
    have(() |- forall(a, forall(b, forall(c, forall(d, (unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))))))) by Rewrite(
      SetTheory.unorderedPair_deconstruction
    )
    andThen(() |- forall(b, forall(c, forall(d, (unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))))))) by InstantiateForall(a)
    andThen(() |- forall(c, forall(d, (unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))))) by InstantiateForall(b)
    andThen(() |- forall(d, (unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))))) by InstantiateForall(c)
    val fwd = andThen(() |- (unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by InstantiateForall(d)

    // backward direction
    //      a = c and b = d => up ab = up cd (and the other case)
    have(() |- unorderedPair(a, b) === unorderedPair(a, b)) by RightRefl
    andThen(Set(a === c, b === d) |- unorderedPair(a, b) === unorderedPair(c, d)) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(x, y)))
    val lhs = andThen(Set((a === c) /\ (b === d)) |- unorderedPair(a, b) === unorderedPair(c, d)) by Rewrite

    have(() |- forall(b, forall(a, unorderedPair(a, b) === unorderedPair(b, a)))) by Rewrite(SetTheory.unorderedPair_symmetry)
    andThen(() |- forall(b, unorderedPair(a, b) === unorderedPair(b, a))) by InstantiateForall(a)
    andThen(() |- (unorderedPair(a, b) === unorderedPair(b, a))) by InstantiateForall(b)
    andThen(Set(a === d, b === c) |- (unorderedPair(a, b) === unorderedPair(c, d))) by RightSubstEq(List((a, d), (b, c)), lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(y, x)))
    val rhs = andThen(Set((a === d) /\ (b === c)) |- (unorderedPair(a, b) === unorderedPair(c, d))) by Rewrite

    have((((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) |- (unorderedPair(a, b) === unorderedPair(c, d))) by LeftOr(lhs, rhs)
    val bwd = andThen(() |- (((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) ==> (unorderedPair(a, b) === unorderedPair(c, d))) by Rewrite

    have(() |- (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by RightIff(fwd, bwd)
  }
  show

  val singletonHasNoExtraElements = makeTHM(
    () |- in(y, singleton(x)) <=> (x === y)
  ) {
    // specialization of the pair axiom to a singleton

    have(() |- in(y, unorderedPair(x, x)) <=> (x === y) \/ (x === y)) by InstFunSchema(Map(x -> x, y -> x, z -> y))(pairAxiom)
    andThen(() |- in(y, singleton(x)) <=> (x === y)) by Restate
  }
  show

  val singletonExtensionality = makeTHM(
    () |- (singleton(x) === singleton(y)) <=> (x === y)
  ) {
    // forward direction
    // {x} === {y} |- x === y
    have(() |- forall(z, in(z, singleton(x)) <=> in(z, singleton(y))) <=> (singleton(x) === singleton(y))) by InstFunSchema(Map(x -> singleton(x), y -> singleton(y)))(extensionalityAxiom)
    andThen((singleton(x) === singleton(y)) |- forall(z, in(z, singleton(x)) <=> in(z, singleton(y)))) by Trivial
    val singiff = andThen((singleton(x) === singleton(y)) |- in(z, singleton(x)) <=> in(z, singleton(y))) by InstantiateForall(z)

    val singX = have(() |- in(z, singleton(x)) <=> (z === x)) by InstFunSchema(Map(y -> z))(singletonHasNoExtraElements)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(x)) <=> in(z, singleton(y))) /\ (in(z, singleton(x)) <=> (z === x))) by RightAnd(singiff, singX)
    val yToX = andThen((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x))) by Trivial

    val singY = have(() |- in(z, singleton(y)) <=> (z === y)) by InstFunSchema(Map(x -> y))(singX)
    have((singleton(x) === singleton(y)) |- (in(z, singleton(y)) <=> (z === x)) /\ (in(z, singleton(y)) <=> (z === y))) by RightAnd(yToX, singY)
    andThen((singleton(x) === singleton(y)) |- ((z === x) <=> (z === y))) by Trivial
    andThen((singleton(x) === singleton(y)) |- ((x === x) <=> (x === y))) by InstFunSchema(Map(z -> x))

    andThen((singleton(x) === singleton(y)) |- (x === y)) by Rewrite
    val fwd = andThen(() |- (singleton(x) === singleton(y)) ==> (x === y)) by Trivial

    // backward direction
    //  x === y |- {x} === {y}
    have(() |- singleton(x) === singleton(x)) by RightRefl
    andThen((x === y) |- singleton(x) === singleton(y)) by RightSubstEq(List((x, y)), lambda(a, singleton(x) === singleton(a)))
    val bwd = andThen(() |- (x === y) ==> (singleton(x) === singleton(y))) by Rewrite

    have(() |- (singleton(x) === singleton(y)) <=> (x === y)) by RightIff(fwd, bwd)
  }
  show

  /**
   * Two ordered pairs are equal iff their elements are equal when taken in order.
   *
   *  pair(a, b) === {{a}, {a, b}}
   *
   *  pair(a, b) === pair(c, d) iff a === c and b === d
   */
  // val pairExtensionality = makeTHM(
  //     () |- (pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))
  // ) {
  //     // forward direction
  //     //  (a === c) /\ (b === d) |- pair a b === pair c d

  //     have(() |- (pair(a, b) === pair(a, b))) by RightRefl
  //     andThen(Set((a === c), (b === d)) |- (pair(a, b) === pair(c, d))) by RightSubstEq(List((a, c), (b, d)), lambda(Seq(x, y), pair(a, b) === pair(x, y)))
  //     val fwd = andThen(() |- ((a === c) /\ (b === d)) ==> (pair(a, b) === pair(c, d))) by Rewrite

  //     // backward direction
  //     //  pair a b === pair c d |- (a === c) /\ (b === d)

  //     val oPairAxAB = have(() |- in(z, pair(a, b)) <=> ((unorderedPair(a, b) === z) \/ (singleton(a) === z))) by InstFunSchema(Map(y -> singleton(a), x -> unorderedPair(a, b)))(pairAxiom)
  //     val oPairAxCD = have(() |- in(z, pair(c, d)) <=> ((unorderedPair(c, d) === z) \/ (singleton(c) === z))) by InstFunSchema(Map(a -> c, b -> d))(oPairAxAB)

  //     have(() |- forall(z, in(z, pair(a, b)) <=> in(z, pair(c, d))) <=> (pair(a, b) === pair(c, d))) by InstFunSchema(Map(x -> pair(a, b), y -> pair(c, d)))(extensionalityAxiom)
  //     andThen((pair(a, b) === pair(c, d)) |- forall(z, in(z, pair(a, b)) <=> in(z, pair(c, d)))) by Trivial
  //     val eqIff = andThen((pair(a, b) === pair(c, d)) |- in(z, pair(a, b)) <=> in(z, pair(c, d))) by InstantiateForall(z)

  //     have((pair(a, b) === pair(c, d)) |- (in(z, pair(a, b)) <=> in(z, pair(c, d))) /\ (in(z, pair(a, b)) <=> ((singleton(a) === z) \/ (unorderedPair(a, b) === z)))) by RightAnd(oPairAxAB, eqIff)
  //     val cdToab = andThen((pair(a, b) === pair(c, d)) |- (in(z, pair(c, d)) <=> ((singleton(a) === z) \/ (unorderedPair(a, b) === z)))) by Trivial

  //     have((pair(a, b) === pair(c, d)) |- (in(z, pair(c, d)) <=> ((singleton(a) === z) \/ (unorderedPair(a, b) === z))) /\ (in(z, pair(c, d)) <=> ((singleton(c) === z) \/ (unorderedPair(c, d) === z)))) by RightAnd(cdToab, oPairAxCD)
  //     val stmtz = andThen((pair(a, b) === pair(c, d)) |- (((singleton(a) === z) \/ (unorderedPair(a, b) === z)) <=> ((singleton(c) === z) \/ (unorderedPair(c, d) === z)))) by Trivial

  //     // unordered pair extensionality
  //     val upExt = have(() |- (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((b === c) /\ (a === d)))) by Rewrite(unorderedPairExtensionality)
  //     // we will instantiate this to eliminate assumptions for our cases

  //     def upEq(a: Term, b: Term, c: Term, d: Term) = unorderedPair(a, b) === unorderedPair(c, d)
  //     def termEq(a: Term, b: Term, c: Term, d: Term) = (a === c) /\ (b === d)
  //     def upEqIff(a: Term, b: Term, c: Term, d: Term) = upEq(a, b, c, d) <=> termEq(a, b, c, d)

  //     val q = formulaVariable
  //     val w = formulaVariable
  //     val e = formulaVariable
  //     val r = formulaVariable

  //     // a != c
  //     val assumption = (upEq(a, a, a, a) \/ upEq(a, b, a, a)) <=> (upEq(c, c, a, a) \/ upEq(c, d, a, a))
  //     val assumption2 = (upEq(a, a, a, b) \/ upEq(a, b, a, b)) <=> (upEq(c, c, a, b) \/ upEq(c, d, a, b))
  //     val decomposition = Set(upEqIff(a, a, a, a), upEqIff(a, b, a, a), upEqIff(c, c, a, a), upEqIff(c, d, a, a))
  //     val decomposition2 = Set(upEqIff(a, a, a, b), upEqIff(a, b, a, b), upEqIff(c, c, a, b), upEqIff(c, d, a, b))

  //     // case z = {a}
  //     // derive a = c
  //     have((pair(a, b) === pair(c, d)) |- assumption) by InstFunSchema(Map(z -> singleton(a)))(stmtz)
  //     andThen((decomposition + (pair(a, b) === pair(c, d))) |- assumption) by Weakening
  //     andThen((decomposition + (pair(a, b) === pair(c, d))) |- ((termEq(a, a, a, a) \/ termEq(a, b, a, a)) <=> (termEq(c, c, a, a) \/ termEq(c, d, a, a)))) by RightSubstIff(List((upEq(a, a, a, a), termEq(a, a, a, a)), (upEq(a, b, a, a), termEq(a, b, a, a)), (upEq(c, c, a, a), termEq(c, c, a, a)), (upEq(c, d, a, a), termEq(c, d, a, a))), lambda(Seq(q, w, e, r), (q \/ w) <=> (e \/ r)))
  //     val aEqc = andThen((decomposition + (pair(a, b) === pair(c, d))) |- (a === c)) by Rewrite

  //     // then get two cases, in both cases derive the conclusion
  //     have((pair(a, b) === pair(c, d)) |- assumption2) by InstFunSchema(Map(z -> unorderedPair(a, b)))(stmtz)
  //     andThen((decomposition2 + (pair(a, b) === pair(c, d)) + (a === c)) |- assumption2) by Weakening
  //     andThen((decomposition2 + (pair(a, b) === pair(c, d)) + (a === c)) |- ((termEq(a, a, a, b) \/ termEq(a, b, a, b)) <=> (termEq(c, c, a, b) \/ termEq(c, d, a, b)))) by RightSubstIff(List((upEq(a, a, a, b), termEq(a, a, a, b)), (upEq(a, b, a, b), termEq(a, b, a, b)), (upEq(c, c, a, b), termEq(c, c, a, b)), (upEq(c, d, a, b), termEq(c, d, a, b))), lambda(Seq(q, w, e, r), (q \/ w) <=> (e \/ r)))
  //     val caseSplit = andThen((decomposition2 + (pair(a, b) === pair(c, d)) + (a === c)) |- (termEq(c, c, a, b) \/ termEq(c, d, a, b))) by Rewrite

  //     // TODO: finish this proof
  //     // probably by z = {c, d} and then get the other symmetric condition, reduce them together
  //     // too much pain

  // }

  // exercise 1.2
  // there exists no X such that P(X) \subset X

  val setWithElementNonEmpty = makeTHM(
    in(y, x) |- !(x === emptySet())
  ) {
    have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    andThen(in(y, emptySet()) |- ()) by Rewrite
    andThen(Set(in(y, x), (x === emptySet())) |- ()) by LeftSubstEq(List((x, emptySet())), lambda(Seq(x), in(y, x)))
    andThen(in(y, x) |- !(x === emptySet())) by Rewrite
  }
  show

  val setWithNoElementsIsEmpty = makeTHM(
    forall(y, !in(y, x)) |- (x === emptySet())
  ) {
    have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    andThen(() |- Set(!in(y, emptySet()), in(y, x))) by Weakening
    val lhs = andThen(() |- in(y, emptySet()) ==> in(y, x)) by Restate

    have(!in(y, x) |- !in(y, x)) by Hypothesis
    andThen(!in(y, x) |- Set(!in(y, x), in(y, emptySet()))) by Weakening
    val rhs = andThen(!in(y, x) |- in(y, x) ==> in(y, emptySet())) by Restate

    have(!in(y, x) |- in(y, x) <=> in(y, emptySet())) by RightIff(lhs, rhs)
    andThen(forall(y, !in(y, x)) |- in(y, x) <=> in(y, emptySet())) by LeftForall(y)
    val exLhs = andThen(forall(y, !in(y, x)) |- forall(y, in(y, x) <=> in(y, emptySet()))) by RightForall

    have(() |- forall(z, in(z, x) <=> in(z, emptySet())) <=> (x === emptySet())) by InstFunSchema(Map(x -> x, y -> emptySet()))(extensionalityAxiom)
    val exRhs = andThen(() |- forall(y, in(y, x) <=> in(y, emptySet())) <=> (x === emptySet())) by Restate

    have(forall(y, !in(y, x)) |- (forall(y, in(y, x) <=> in(y, emptySet())) <=> (x === emptySet())) /\ forall(y, in(y, x) <=> in(y, emptySet()))) by RightAnd(exLhs, exRhs)
    andThen(forall(y, !in(y, x)) |- (x === emptySet())) by Trivial
  }
  show

  val emptySetIsASubset = makeTHM(
    () |- subset(emptySet(), x)
  ) {
    val lhs = have(() |- subset(emptySet(), x) <=> forall(z, in(z, emptySet()) ==> in(z, x))) by InstFunSchema(Map(x -> emptySet(), y -> x))(subsetAxiom)

    have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(emptySetAxiom)
    andThen(() |- in(y, emptySet()) ==> in(y, x)) by Weakening
    val rhs = andThen(() |- forall(y, in(y, emptySet()) ==> in(y, x))) by RightForall

    have(() |- (subset(emptySet(), x) <=> forall(z, in(z, emptySet()) ==> in(z, x))) /\ forall(y, in(y, emptySet()) ==> in(y, x))) by RightAnd(lhs, rhs)
    andThen(() |- (subset(emptySet(), x) <=> forall(z, in(z, emptySet()) ==> in(z, x))) /\ forall(z, in(z, emptySet()) ==> in(z, x))) by Restate
    andThen(() |- subset(emptySet(), x)) by Trivial
  }
  show

  val powerSetNonEmpty = makeTHM(
    () |- !(powerSet(x) === emptySet())
  ) {
    // strategy
    //      prove power set contains empty set
    //      since it has an element, it is not empty itself

    val lhs = have(() |- in(emptySet(), powerSet(x)) <=> subset(emptySet(), x)) by InstFunSchema(Map(x -> emptySet(), y -> x))(powerAxiom)

    have(() |- (in(emptySet(), powerSet(x)) <=> subset(emptySet(), x)) /\ subset(emptySet(), x)) by RightAnd(lhs, emptySetIsASubset)
    val emptyinPower = andThen(() |- in(emptySet(), powerSet(x))) by Trivial
    val nonEmpty = have(in(emptySet(), powerSet(x)) |- !(powerSet(x) === emptySet())) by InstFunSchema(Map(y -> emptySet(), x -> powerSet(x)))(setWithElementNonEmpty)

    have(() |- !(powerSet(x) === emptySet())) by Cut(emptyinPower, nonEmpty)
  }
  show

  /**
   * Proves that any singleton set is not equal to the empty set
   * // statement
   */
  val singletonNonEmpty = makeTHM(
    () |- !(singleton(x) === emptySet())
  ) {
    val reflLhs = have(() |- in(x, singleton(x)) <=> (x === x)) by InstFunSchema(Map(y -> x))(singletonHasNoExtraElements)

    val reflRhs = have(() |- (x === x)) by RightRefl
    have(() |- (x === x) /\ (in(x, singleton(x)) <=> (x === x))) by RightAnd(reflLhs, reflRhs)
    val lhs = andThen(() |- in(x, singleton(x))) by Trivial

    val rhs = have(in(x, singleton(x)) |- !(singleton(x) === emptySet())) by InstFunSchema(Map(y -> x, x -> singleton(x)))(setWithElementNonEmpty)

    have(() |- !(singleton(x) === emptySet())) by Cut(lhs, rhs)
  }
  show

  // this is imposed by well founded ness of set inclusion
  // expressed by the Axiom of Regularity / Foundation
  val selfNonInclusion = makeTHM(
    () |- !in(x, x)
  ) {
    val X = singleton(x)

    have(() |- !(X === emptySet()) ==> exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))) by InstFunSchema(Map(x -> X))(foundationAxiom)
    val lhs = andThen(!(X === emptySet()) |- exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))) by Restate

    have(in(y, X) |- in(y, X) <=> (x === y)) by Weakening(singletonHasNoExtraElements)
    val innerRhs = andThen(in(y, X) |- (x === y)) by Trivial

    have(Set(in(x, X), (in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by Hypothesis
    andThen(Set(in(x, X), forall(z, in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by LeftForall(z)
    andThen(Set(in(x, X), forall(z, in(z, X) ==> !in(z, x)), in(x, X)) |- in(x, X) ==> !in(x, x)) by InstFunSchema(Map(z -> x, y -> x))
    val coreRhs = andThen(in(x, X) /\ forall(z, in(z, X) ==> !in(z, x)) |- !in(x, x)) by Restate

    // now we need to show that the assumption is indeed true
    // this requires destruction of the existential quantifier in lhs
    have(in(x, X) /\ forall(z, in(z, X) ==> !in(z, x)) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Hypothesis
    val innerRhs2 = andThen(Set(in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)), x === y) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by LeftSubstEq(
      List((x, y)),
      lambda(Seq(y), in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))
    )

    have(Set(in(y, X), in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Cut(innerRhs, innerRhs2)
    andThen(in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Restate
    val coreLhs = andThen(exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by LeftExists

    val rhs = have(exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- !in(x, x)) by Cut(coreLhs, coreRhs)

    val finRhs = have(!(X === emptySet()) |- !in(x, x)) by Cut(lhs, rhs)
    val finLhs = have(() |- !(X === emptySet())) by Rewrite(singletonNonEmpty)

    have(() |- !in(x, x)) by Cut(finLhs, finRhs)
  }
  show

  val powerSetNonInclusion = makeTHM(
    Exists(x, properSubset(powerSet(x), x)) |- ()
  ) {
    val lhs = have(subset(powerSet(x), x) |- subset(powerSet(x), x)) by Hypothesis

    val rhs = have(() |- in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x)) by InstFunSchema(Map(x -> powerSet(x), y -> x))(powerAxiom)

    have(subset(powerSet(x), x) |- subset(powerSet(x), x) /\ (in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x))) by RightAnd(lhs, rhs)
    val contraLhs = andThen(subset(powerSet(x), x) |- in(powerSet(x), powerSet(x))) by Trivial

    val contraRhs = have(() |- !in(powerSet(x), powerSet(x))) by InstFunSchema(Map(x -> powerSet(x)))(selfNonInclusion)

    have(subset(powerSet(x), x) |- !in(powerSet(x), powerSet(x)) /\ in(powerSet(x), powerSet(x))) by RightAnd(contraLhs, contraRhs)
    andThen(subset(powerSet(x), x) |- ()) by Restate
    andThen(subset(powerSet(x), x) |- (x === powerSet(x))) by Weakening
    andThen(properSubset(powerSet(x), x) |- ()) by Restate
    andThen(exists(x, properSubset(powerSet(x), x)) |- ()) by LeftExists
  }
  show

  // exercise 1.3

}
