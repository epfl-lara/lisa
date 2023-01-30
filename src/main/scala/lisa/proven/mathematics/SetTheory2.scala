package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.prooflib.Library
import lisa.utils.Printer
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib
import lisa.proven.mathematics.Jechcercises

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

  // relation and function symbols
  val r = variable
  val f = variable
  val g = variable

  val P = predicate(1)
  val Q = predicate(1)
  val schemPred = predicate(1)


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

  /**
   * 
   * The unary union operation unfolds a singleton into the single element
   *      \forall x. U {x} === x
   **/
  val unionOfSingletonIsTheOriginalSet = makeTHM(
    () |- (union(singleton(x)) === x)
  ) {
    val X = singleton(x)

    // need to prove:
    //    \forall z. z \in U X <=> z \in x

    // forward direction
    //  z \in x |- z \in U X
    val unionAx = have(() |- in(z, union(X)) <=> exists(y, in(z, y) /\ in(y, X))) by InstFunSchema(Map(x -> z, z -> X))(unionAxiom)
    andThen(in(z, union(X)) |- exists(y, in(z, y) /\ in(y, X))) by Trivial

    val andLhs = have(() |- in(x, X)) by InstFunSchema(Map(y -> x))(firstElemInPair)
    val andRhs = have(in(z, x) |- in(z, x)) by Hypothesis
    have(in(z, x) |- in(z, x) /\ in(x, X)) by RightAnd(andLhs, andRhs)
    val fwdLhs = andThen(in(z, x) |- exists(y, in(z, y) /\ in(y, X))) by RightExists(x)
    have(in(z, x) |- exists(y, in(z, y) /\ in(y, X)) /\ (in(z, union(X)) <=> exists(y, in(z, y) /\ in(y, X)))) by RightAnd(fwdLhs, unionAx)
    andThen(in(z, x) |- in(z, union(X))) by Trivial
    val fwd = andThen(() |- in(z, x) ==> in(z, union(X))) by Rewrite

    // backward direction
    //  z \in U X |- z \in x

    have(in(y, X) |- in(y, X)) by Hypothesis
    val bwdHypo = andThen(in(z, y) /\ in(y, X) |- in(y, X)) by Weakening
    have(in(z, y) /\ in(y, X) |- in(y, X) /\ (in(y, X) <=> (x === y))) by RightAnd(bwdHypo, Jechcercises.singletonHasNoExtraElements)
    val cutLhs = andThen(in(z, y) /\ in(y, X) |- (x === y)) by Trivial

    have(in(z, y) |- in(z, y)) by Hypothesis
    andThen(in(y, X) /\ in(z, y) |- in(z, y)) by Weakening
    val cutRhs = andThen(Set(in(z, y) /\ in(y, X), (x === y)) |- in(z, x)) by RightSubstEq(List((y, x)), lambda(y, in(z, y)))

    have(in(z, y) /\ in(y, X) |- in(z, x)) by Cut(cutLhs, cutRhs)
    val bwdRhs = andThen(exists(y, in(z, y) /\ in(y, X)) |- in(z, x)) by LeftExists
    val bwdLhs = have(in(z, union(X)) |- exists(y, in(z, y) /\ in(y, X))) by Weakening(unionAx)
    have(in(z, union(X)) |- in(z, x)) by Cut(bwdLhs, bwdRhs)
    val bwd = andThen(() |- in(z, union(X)) ==> in(z, x)) by Rewrite

    have(() |- in(z, union(X)) <=> in(z, x)) by RightIff(fwd, bwd)
    val iff = andThen(() |- forall(z, in(z, union(X)) <=> in(z, x))) by RightForall

    val extAx = have(() |- forall(z, in(z, union(X)) <=> in(z, x)) <=> (union(X) === x)) by InstFunSchema(Map(x -> union(X), y -> x))(extensionalityAxiom)

    have(() |- forall(z, in(z, union(X)) <=> in(z, x)) /\ (forall(z, in(z, union(X)) <=> in(z, x)) <=> (union(X) === x))) by RightAnd(iff, extAx)
    andThen(() |- (union(X) === x)) by Trivial
  }
  show

  /**
   * Chapter 1
   */

  val russelsParadox = makeTHM(
    exists(x, forall(y, ! in(y, y) <=> in(y, x))) |- ()
  ) {
    val contra = !in(x, x) <=> in(x, x)

    have(contra |- ()) by Restate
    andThen(forall(y, ! in(y, y) <=> in(y, x)) |- ()) by LeftForall(x)
    andThen(exists(x, forall(y, ! in(y, y) <=> in(y, x))) |- ()) by LeftExists
  }
  show

  val noUniversalSet = makeTHM(
    forall(z, in(z, x)) |- ()
  ) {
    have(in(x, x) |- ()) by Rewrite(Jechcercises.selfNonInclusion)
    andThen(forall(z, in(z, x)) |- ()) by LeftForall(x)
  }
  show

  // predicates for properties of sets

  // operations on sets

  /**
   * Generic proof for uniqueness under assumption of existence
   * 
   * to use:
   * have(exists(z, forall(t, in(t, z) <=> myProperty(t))) |- existsOne(z, forall(t, in(t, z) <=> myProperty(t)))) by InstPredSchema(Map(schemPred -> (t, myProperty(t))))
   * 
   * Instantiation will fail if myProperty(t) contains z as a free variable
   */
  val uniquenessByDefinition = makeTHM (
    exists(z, forall(t, in(t, z) <=> schemPred(t))) |- existsOne(z, forall(t, in(t, z) <=> schemPred(t)))
  ) {
    def prop(z: Term) = in(t, z) <=> schemPred(t)
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
    andThen(exists(z, fprop(z)) |- existsOne(z, fprop(z))) by RightExistsOne
  }
  show

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
    val prop = (in(t, x) /\ in(t, y))
    def fprop(z: Term) = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop(z)) |- existsOne(z, fprop(z))) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)

    // assumption elimination
    // in essence, an existence proof
    val existsLhs = have(() |- exists(z, fprop(z))) by Rewrite(setIntersectionExistence)

    have(() |- existsOne(z, fprop(z))) by Cut(existsLhs, existsRhs)
  }
  show

  val setIntersection = DEF (x, y) --> The (z, forall(t, in(t, z) <=> (in(t, x) /\ in(t, y))))(setIntersectionUniqueness)

  val unaryIntersectionExistence = makeTHM (
    () |- exists(z, forall(t, in(t, z) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))
  ) {

    // the unary intersection is a filtering on the unary union
    // we apply the comprehension schema on this fact and then deconstruct as required

    have(() |- exists(y, forall(x, in(x, y) <=> (in(x, union(z)) /\ sPhi(x, union(z)))))) by InstFunSchema(Map(z -> union(z)))(comprehensionSchema)
    andThen(() |- exists(y, forall(x, in(x, y) <=> (in(x, union(z)) /\ forall(b, in(b, z) ==> in(x, b)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(x, t), forall(b, in(b, z) ==> in(x, b)))))
    andThen(() |- exists(a, forall(t, in(t, a) <=> (in(t, union(z)) /\ forall(b, in(b, z) ==> in(t, b)))))) by Restate
    andThen(() |- exists(a, forall(t, in(t, a) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))) by InstFunSchema(Map(z -> x))
  }
  show

  val unaryIntersectionUniqueness = makeTHM (
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))
  ) {
    val prop = (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))
    def fprop(z: Term) = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop(z)) |- existsOne(z, fprop(z))) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)

    val existsLhs = have(() |- exists(z, fprop(z))) by Rewrite(unaryIntersectionExistence)

    have(() |- existsOne(z, fprop(z))) by Cut(existsLhs, existsRhs)
  }
  show

  val unaryintersection = DEF (x) -> The (z, forall(t, in(t, z) <=> (in(t, union(x)) /\ forall(b, in(b, x) ==> in(t, b)))))(unaryIntersectionUniqueness)

  val setDifferenceExistence = makeTHM (
    () |- exists(a, forall(t, in(t, a) <=> (in(t, x) /\ !in(t, y))))
  ) {
    // set difference is a filtering of the first set based on the second
    // so we apply comprehension schema

    have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, b))))) by InstPredSchema(Map(sPhi -> lambda(Seq(x, z), !in(x, b))))(comprehensionSchema)
    andThen(() |- exists(a, forall(t, in(t, a) <=> (in(t, z) /\ !in(t, b))))) by Restate
    andThen(() |- exists(a, forall(t, in(t, a) <=> (in(t, x) /\ !in(t, y))))) by InstFunSchema(Map(z -> x, b -> y))
  }
  show

  val setDifferenceUniqueness = makeTHM (
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))
  ) {
    val prop = (in(t, x) /\ !in(t, y))
    def fprop(z: Term) = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop(z)) |- existsOne(z, fprop(z))) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)

    val existsLhs = have(() |- exists(z, fprop(z))) by Rewrite(setDifferenceExistence)

    have(() |- existsOne(z, fprop(z))) by Cut(existsLhs, existsRhs)
  }
  show

  val setDifference = DEF (x, y) --> The (z, forall(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))(setDifferenceUniqueness)

  val setUnion = DEF (x, y) --> union(unorderedPair(x, y))

  // inductive set
  // 0 \in x, \forall y \in x. y U {y} \in x
  def inductive(x: Term) = in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, singleton(y))), x))

  // axiom of infinity
  // () |- exists(x, inductive(x))

  /**
   * There exists a set that is the intersection of all sets satisfying a given formula
   * With classes, this means that the unary intersection of a class defined by a predicate is a set.
   */
  val intersectionOfPredicateClassExists = makeTHM(
    exists(x, P(x)) |- exists(z, forall(t, in(t, z) <=> forall(y, P(y) ==> in(t, y))))
  ) {
    have(() |- exists(z, forall(t, in(t, z) <=> (in(t, x) /\ sPhi(t, x))))) by InstFunSchema(Map(z -> x))(comprehensionSchema)
    val conjunction = andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, x), forall(y, P(y) ==> in(t, y)))))

    have(forall(y, P(y) ==> in(t, y)) |- forall(y, P(y) ==> in(t, y))) by Hypothesis
    andThen(forall(y, P(y) ==> in(t, y)) /\ P(x) |- forall(y, P(y) ==> in(t, y))) by Weakening
    andThen(forall(y, P(y) ==> in(t, y)) /\ P(x) |- P(x) ==> in(t, x)) by InstantiateForall(x)
    andThen(forall(y, P(y) ==> in(t, y)) /\ P(x) |- in(t, x) /\ forall(y, P(y) ==> in(t, y))) by Trivial
    val fwd = andThen(P(x) |- forall(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Rewrite

    have((in(t, x) /\ forall(y, P(y) ==> in(t, y))) |- (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Hypothesis
    val bwd = andThen(() |- (in(t, x) /\ forall(y, P(y) ==> in(t, y))) ==> (forall(y, P(y) ==> in(t, y)))) by Rewrite

    val lhs = have(P(x) |- forall(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by RightIff(fwd, bwd)

    val form = formulaVariable
    have((in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) |- in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))) by Hypothesis
    val rhs = andThen(Set((in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))), (forall(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))) |- (in(t, z) <=> (forall(y, P(y) ==> in(t, y))))) by RightSubstIff(List((forall(y, P(y) ==> in(t, y)), (in(t, x) /\ forall(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))
  
    have(Set(P(x), (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))) |- in(t, z) <=> (forall(y, P(y) ==> in(t, y)))) by Cut(lhs, rhs)
    andThen(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- in(t, z) <=> (forall(y, P(y) ==> in(t, y)))) by LeftForall(t)
    andThen(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y))))) by RightForall
    andThen(Set(P(x), forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y)))))) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by RightExists(z)
    val cutRhs = andThen(Set(P(x), exists(z, forall(t, (in(t, z) <=> (in(t, x) /\ forall(y, P(y) ==> in(t, y))))))) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by LeftExists
    
    have(P(x) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by Cut(conjunction, cutRhs)
    andThen(exists(x, P(x)) |- exists(z, forall(t, in(t, z) <=> (forall(y, P(y) ==> in(t, y)))))) by LeftExists

  }
  show

  /**
   * Cartesian Products
   */

  val cartesianProductExistence = makeTHM(
    () |- exists(z, forall(t, in(t, z) <=> (in(t, powerSet(unorderedPair(x, y))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))
  ) {
    val ztemp = variable
    val ppxy = powerSet(unorderedPair(x, y))
    have(() |- exists(y, forall(x, in(x, y) <=> (in(x, ztemp) /\ sPhi(x, ztemp))))) by InstFunSchema(Map(z -> ztemp))(comprehensionSchema)
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, ztemp) /\ sPhi(t, ztemp))))) by Restate
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, ppxy) /\ sPhi(t, ppxy))))) by InstFunSchema(Map(ztemp -> ppxy))
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, ppxy) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, z), exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))
  }
  show

  val cartesianProductUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, powerSet(unorderedPair(x, y))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))
  ) {
    val prop = (in(t, powerSet(unorderedPair(x, y))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))
    val fprop = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop) |- existsOne(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)
    val existsLhs = have(() |- exists(z, fprop)) by Rewrite(cartesianProductExistence)

    have(() |- existsOne(z, fprop)) by Cut(existsLhs, existsRhs)
  }
  show

  val cartesianProduct = DEF (x, y) --> The(z, forall(t, in(t, z) <=> (in(t, powerSet(unorderedPair(x, y))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, x) /\ in(a, y))))))(cartesianProductUniqueness)
  
  // binary relations

  val relation = DEF (r, x) --> subset(r, cartesianProduct(x, x))

  val relationDomainExistence = makeTHM(
    () |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r)))) /\ exists(a, in(pair(t, a), r))))
  ) {
    val ztemp = variable
    have(() |- exists(y, forall(x, in(x, y) <=> (in(x, ztemp) /\ sPhi(x, ztemp))))) by InstFunSchema(Map(z -> ztemp))(comprehensionSchema)
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, ztemp) /\ sPhi(t, ztemp))))) by Restate
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ sPhi(t, union(union(r))))))) by InstFunSchema(Map(ztemp -> union(union(r))))
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, x), exists(a, in(pair(t, a), r)))))
  }
  show

  val relationDomainUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r)))) /\ exists(a, in(pair(t, a), r))))
  ) {
    val prop = (in(t, union(union(r)))) /\ exists(a, in(pair(t, a), r))
    val fprop = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop) |- existsOne(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)
    val existsLhs = have(() |- exists(z, fprop)) by Rewrite(relationDomainExistence)

    have(() |- existsOne(z, fprop)) by Cut(existsLhs, existsRhs)
  }
  show

  val relationDomain = DEF (r) --> The(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(t, a), r)))))(relationDomainUniqueness)

  val relationRangeExistence = makeTHM(
    () |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))
  ) {
    val ztemp = variable
    have(() |- exists(y, forall(x, in(x, y) <=> (in(x, ztemp) /\ sPhi(x, ztemp))))) by InstFunSchema(Map(z -> ztemp))(comprehensionSchema)
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, ztemp) /\ sPhi(t, ztemp))))) by Restate
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ sPhi(t, union(union(r))))))) by InstFunSchema(Map(ztemp -> union(union(r))))
    andThen(() |- exists(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, x), exists(a, in(pair(a, t), r)))))
  }
  show

  val relationRangeUniqueness = makeTHM(
    () |- existsOne(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))
  ) {
    val prop = (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))
    val fprop = forall(t, in(t, z) <=> prop)

    val existsRhs = have(exists(z, fprop) |- existsOne(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)
    val existsLhs = have(() |- exists(z, fprop)) by Rewrite(relationRangeExistence)

    have(() |- existsOne(z, fprop)) by Cut(existsLhs, existsRhs)
  }
  show

  val relationRange = DEF (r) --> The(z, forall(t, in(t, z) <=> (in(t, union(union(r))) /\ exists(a, in(pair(a, t), r)))))(relationRangeUniqueness)

  val relationField = DEF (r) --> (setUnion(relationDomain(r), relationRange(r)))

  val functionalOver = DEF (f, x) --> (relation(f, x) /\ forall(x, in(x, relationDomain(f)) ==> existsOne(y, in(y, relationRange(f)) /\ in(pair(x, y), f))))

  val functional = DEF (f) --> functionalOver(f, relationDomain(f))


  val restrictedFunctionExistence = makeTHM(
    () |- exists(g, forall(t, in(t, g) <=> (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))
  ) {
    have(() |- exists(g, forall(t, in(t, g) <=> (in(t, z) /\ sPhi(t, z))))) by Rewrite(comprehensionSchema)
    andThen(() |- exists(g, forall(t, in(t, g) <=> (in(t, f) /\ sPhi(t, f))))) by InstFunSchema(Map(z -> f))
    andThen(() |- exists(g, forall(t, in(t, g) <=> (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))) by InstPredSchema(Map(sPhi -> lambda(Seq(t, f), exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))
  }

  val restrictedFunctionUniqueness = makeTHM(
    () |- existsOne(g, forall(t, in(t, g) <=> (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))
  ) {
    val prop = (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))
    val fprop = forall(t, in(t, g) <=> prop)

    val existsRhs = have(exists(g, fprop) |- existsOne(g, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniquenessByDefinition)
    val existsLhs = have(() |- exists(g, fprop)) by Rewrite(restrictedFunctionExistence)

    have(() |- existsOne(g, fprop)) by Cut(existsLhs, existsRhs)
  }

  /**
   * The restriction of a function `f` to a set `x`
   * 
   * restrictedFunction(f, x) === {(y, f(y)) | y \in x},
   * 
   * also written as f_x.
   * 
   */
  val restrictedFunction = DEF (f, x) --> The(g, forall(t, in(t, g) <=> (in(t, f) /\ exists(y, exists(z, in(y, x) /\ (t === pair(y, z)))))))(restrictedFunctionUniqueness)

  /**
   * 
   * Sigma Pi Lambda
   * 
   */

  /**
   * TODO: write something
   */
  val Sigma = DEF (x, f) --> union(restrictedFunction(f, x))

  val piExistence = makeTHM(
    () |- exists(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))
  ) {
    val ztemp = variable
    have(() |- exists(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ sPhi(g, powerSet(Sigma(x, f))))))) by InstFunSchema(Map(z -> powerSet(Sigma(x, f))))(comprehensionSchema)
    andThen(() |- exists(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))) by InstPredSchema(Map(sPhi -> lambda(Seq(g, z), (subset(x, relationDomain(g)) /\ functional(g)))))
  }

  val piUniqueness = makeTHM(
    () |- existsOne(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))
  ) {
    val prop = (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))
    val fprop = forall(g, in(g, z) <=> prop)

    val existsRhs = have(exists(z, fprop) |- existsOne(z, fprop)) by InstPredSchema(Map(schemPred -> (g, prop)))(uniquenessByDefinition)
    val existsLhs = have(() |- exists(z, fprop)) by Rewrite(piExistence)

    have(() |- existsOne(z, fprop)) by Cut(existsLhs, existsRhs)
  }

  /**
   * TODO: write something
   */
  val Pi = DEF (x, f) --> The(z, forall(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))(piUniqueness)

  /**
   * Properties of relations
   */

   val reflexive  = DEF (r, x) --> relation(r, x) /\ forall(y, in(y, x) ==> in(pair(y, y), r))
   val symmetric  = DEF (r, x) --> relation(r, x) /\ forall(y, forall(z, in(pair(y, z), r) <=> in(pair(z, y), r)))
   val transitive = DEF (r, x) --> relation(r, x) /\ forall(w, forall(y, forall(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))))
   val equivalence = DEF (r, x) --> reflexive(r, x) /\ symmetric(r, x) /\ transitive(r, x)

   val antiReflexive = DEF (r, x) --> relation(r, x) /\ forall(y, in(y, x) ==> !in(pair(y, y), r))
   val irreflexive = antiReflexive
   val antiSymmetric = DEF (r, x) --> relation(r, x) /\ forall(y, forall(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))
   val asymmetric = DEF (r, x) --> relation(r, x) /\ forall(y, forall(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))

   val connected = DEF (r, x) --> relation(r, x) /\ forall(y, forall(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z))))
   val total = connected
   val stronglyConnected = DEF (r, x) --> relation(r, x) /\ forall(y, forall(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r))))

}
