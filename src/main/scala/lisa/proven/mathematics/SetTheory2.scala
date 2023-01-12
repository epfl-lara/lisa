package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.proven.mathematics.Jechcercises
import lisa.utils.Library
import lisa.utils.Printer
import lisa.utils.tactics.BasicStepTactic.*
import lisa.utils.tactics.ProofTacticLib

/**
 * An embryo of mathematical development, containing a few example theorems and the definition of the ordered unorderedPair.
 */
object SetTheory2 extends lisa.proven.mathematics.BasicDefs {

  // var defs
  val x = variable
  val y = variable
  val z = variable
  val t = variable
  val a = variable
  val b = variable
  val c = variable

  val P = predicate(1)
  val Q = predicate(1)


  /**
   * Properties about pairs
   */

  val firstElemInPair = makeTHM(
    () |- in(x, unorderedPair(x, y))
  ) {
    val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstFunSchema(Map(x -> x, y -> y, z -> z))(ax"pairAxiom")
    have((z === x) |- (z === x)) by Hypothesis
    val rhs = andThen((z === x) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === x) |-  (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    andThen((z === x) |- in(z, unorderedPair(x, y))) by Trivial
    andThen((x === x) |- in(x, unorderedPair(x, y))) by InstFunSchema(Map(z -> x))
    andThen(() |- in(x, unorderedPair(x, y))) by LeftRefl
  }
  show

  val secondElemInPair = makeTHM(
    () |- in(y, unorderedPair(x, y))
  ) {
    val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstFunSchema(Map(x -> x, y -> y, z -> z))(ax"pairAxiom")
    have((z === y) |- (z === y)) by Hypothesis
    val rhs = andThen((z === y) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === y) |-  (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    andThen((z === y) |- in(z, unorderedPair(x, y))) by Trivial
    andThen((y === y) |- in(y, unorderedPair(x, y))) by InstFunSchema(Map(z -> y))
    andThen(() |- in(y, unorderedPair(x, y))) by LeftRefl
  }
  show

  // val unionOfOrderedPairIsUnordered = makeTHM(
  //   () |- union(pair(x, y)) === unorderedPair(x, y)
  // ) {
  //   val upAxiom = ax"unorderedPair"
    
  //   /**
  //    * strategy
  //    * prove:
  //    *    lhs
  //    *    () |- z in uPair(x, y) <=> z is x or z is y
  //    *    rhs
  //    *    () |- z in oPair(x, y) <=> z is x or z is y
  //    * 
  //    * derive z in uPair(x, y) <=> z in oPair(x, y) and apply extensionality
  //    */

  //   // val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by Instantiateforall(x, y, z)(upAxiom)


  // }

  // other theorems I want to prove:
  // () |- union(singleton(x)) = x

  /**
   * Chapter 1
   */

  val russelsParadox = makeTHM(
    exists(x, forall(y, ! in(y, y) <=> in(y, x))) |- ()
  ) {
    have(forall(y, ! in(y, y) <=> in(y, x)) |- forall(y, ! in(y, y) <=> in(y, x))) by Hypothesis
    andThen(forall(y, ! in(y, y) <=> in(y, x)) |- (!in(x, x)) <=> in(x, x)) by InstantiateForall(x)
    andThen(forall(y, ! in(y, y) <=> in(y, x)) |- ()) by Rewrite
    andThen(exists(x, forall(y, ! in(y, y) <=> in(y, x))) |- ()) by LeftExists
  }
  show

  val noUniversalSet = makeTHM(
    forall(z, in(z, x)) |- ()
  ) {
    val selfNonInclusion = Jechcercises.selfNonInclusion
    have(in(x, x) |- ()) by Rewrite(thm"selfNonInclusion")
    andThen(forall(z, in(z, x)) |- ()) by LeftForall(x)
  }
  show

  // predicates for properties of sets

  // operations on sets

  val setIntersectionExistence = makeTHM (
    () |- exists(a, forall(t, in(t, a) <=> (in(t, x) /\ in(t, y))))
  ) {
    // note that the intersection is a filtering of either x or y based on the other
    // so we apply comprehension schema

    have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ in(x, b))))) by InstPredSchema(Map(sPhi -> lambda(Seq(x, z), in(x, b))))(comprehensionSchema)
    andThen(() |- exists(a, forall(t, in(t, a) <=> (in(t, z) /\ in(t, b))))) by Restate
    andThen(() |- exists(a, forall(t, in(t, a) <=> (in(t, x) /\ in(t, y))))) by InstFunSchema(Map(z -> x, b -> y))
  }
  show

  val setIntersectionUniqueness = makeTHM (
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ in(t, y))))
  ) {
    def prop(z: Term) = in(t, z) <=> (in(t, x) /\ in(t, y))
    def fprop(z: Term) = forall(t, prop(z))

    // forward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    andThen(fprop(z) /\ (z === a) |- fprop(z)) by Weakening
    andThen(Set(fprop(z) /\ (z === a), (z === a)) |- fprop(a)) by RightSubstEq(List((z, a)), lambda(Seq(z), fprop(z)))
    val forward = andThen(fprop(z) |- (z === a) ==> fprop(a)) by Restate

    // backward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    val instLhs = andThen(fprop(z) |- prop(z)) by InstantiateForall(t)
    val instRhs = andThen(fprop(a) |- prop(a)) by InstFunSchema(Map(z -> a))
    
    have(Set(fprop(z), fprop(a)) |- prop(z) /\ prop(a)) by RightAnd(instLhs, instRhs)
    andThen(fprop(z) /\ fprop(a) |- in(t, a) <=> in(t, z)) by Trivial
    val extLhs = andThen(fprop(z) /\ fprop(a) |- forall(t, in(t, a) <=> in(t, z))) by RightForall
    val extRhs = have(() |- forall(t, in(t, a) <=> in(t, z)) <=> (a === z)) by InstFunSchema(Map(x -> a, y -> z))(extensionalityAxiom)

    have(fprop(z) /\ fprop(a) |- (forall(t, in(t, a) <=> in(t, z)) <=> (a === z)) /\ forall(t, in(t, a) <=> in(t, z))) by RightAnd(extLhs, extRhs)
    andThen(fprop(z) /\ fprop(a) |- (a === z)) by Trivial
    val backward = andThen(fprop(z) |- fprop(a) ==> (a === z)) by Restate

    have(fprop(z) |- fprop(a) <=> (a === z)) by RightIff(forward, backward)
    andThen(fprop(z) |- forall(a, fprop(a) <=> (a === z))) by RightForall
    andThen(fprop(z) |- exists(z, forall(a, fprop(a) <=> (a === z)))) by RightExists(z)
    andThen(exists(z, fprop(z)) |- exists(z, forall(a, fprop(a) <=> (a === z)))) by LeftExists
    val existsRhs = andThen(exists(z, fprop(z)) |- existsOne(z, fprop(z))) by RightExistsOne

    // assumption elimination
    // in essence, an existence proof
    val existsLhs = have(() |- exists(z, fprop(z))) by Rewrite(setIntersectionExistence)

    have(() |- existsOne(z, fprop(z))) by Cut(existsLhs, existsRhs)
  }
  show

  val setIntersection = DEF (x, y) --> The (z, forall(t, in(t, z) <=> (in(t, x) /\ in(t, y))))(setIntersectionUniqueness)
  // val intersection = DEF (x) -> The (z, forall(t, in(t, z) <=> forall(a, in(a, x) /\ in(a, t))))

  // inductive set
  // 0 \in x, \forall y \in x. y U {y} \in x
  def inductive(x: Term) = in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, singleton(y))), x))

  // axiom of infinity
  // () |- exists(x, inductive(x))

  

}
