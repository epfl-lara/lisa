package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Library
import lisa.utils.Printer
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.utils.tactics.BasicStepTactic.*
import lisa.utils.tactics.ProofTacticLib
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

  val P = predicate(1)
  val Q = predicate(1)


  /**
   * Properties about pairs
   */

  val firstElemInPair = makeTHM(
    () |- in(x, unorderedPair(x, y))
  ) {
    val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstantiateForall(Seq(x: Term, y: Term, z: Term): _*)(ax"pairAxiom")
    have((z === x) |- (z === x)) by Hypothesis
    val rhs = andThen((z === x) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === x) |-  (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    andThen((z === x) |- in(z, unorderedPair(x, y))) by Trivial
    andThen((x === x) |- in(x, unorderedPair(x, y))) by InstFunSchema(Map(z -> lambda(Seq(), x)))
    andThen(() |- in(x, unorderedPair(x, y))) by LeftRefl
  }
  show

  val secondElemInPair = makeTHM(
    () |- in(y, unorderedPair(x, y))
  ) {
    val lhs = have(() |- in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by InstantiateForall(Seq(x: Term, y: Term, z: Term): _*)(ax"pairAxiom")
    have((z === y) |- (z === y)) by Hypothesis
    val rhs = andThen((z === y) |- (z === x) \/ (z === y)) by Rewrite
    val factset = have((z === y) |-  (in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) /\ ((z === x) \/ (z === y))) by RightAnd(lhs, rhs)

    andThen((z === y) |- in(z, unorderedPair(x, y))) by Trivial
    andThen((y === y) |- in(y, unorderedPair(x, y))) by InstFunSchema(Map(z -> lambda(Seq(), y)))
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
  
  
}
