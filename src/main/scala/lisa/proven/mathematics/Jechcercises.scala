package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Library
import lisa.utils.Helpers._
import lisa.utils.Printer
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.utils.tactics.BasicStepTactic.*
import lisa.utils.tactics.ProofTacticLib

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
    // val pairExtensionality = makeTHM(
    //     () |- (pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))
    // ) {

    // }

    // exercise 1.2
    // there exists no X such that P(X) \subset X

    val setWithElementNonEmpty = makeTHM(
        in(y, x) |- !(x === emptySet())
    ) {
        have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(ax"EmptySet")
        andThen(in(y, emptySet()) |- ()) by Rewrite
        andThen(Set(in(y, x), (x === emptySet())) |- ()) by LeftSubstEq(List((x, emptySet())), lambda(Seq(x), in(y, x)))
        andThen(in(y, x) |- !(x === emptySet())) by Rewrite
    }
    show

    val setWithNoElementsIsEmpty = makeTHM(
        forall(y, !in(y, x)) |- (x === emptySet())
    ) {
        have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(ax"EmptySet")
        andThen(() |- Set(!in(y, emptySet()), in(y, x))) by Weakening
        val lhs = andThen(() |- in(y, emptySet()) ==> in(y, x)) by Restate

        have(!in(y, x) |- !in(y, x)) by Hypothesis
        andThen(!in(y, x) |- Set(!in(y, x), in(y, emptySet()))) by Weakening
        val rhs = andThen(!in(y, x) |- in(y, x) ==> in(y, emptySet())) by Restate

        have(!in(y, x) |- in(y, x) <=> in(y, emptySet())) by RightIff(lhs, rhs)
        andThen(forall(y, !in(y, x)) |- in(y, x) <=> in(y, emptySet())) by LeftForall(y)
        val exLhs = andThen(forall(y, !in(y, x)) |- forall(y, in(y, x) <=> in(y, emptySet()))) by RightForall

        have(() |- forall(z, in(z, x) <=> in(z, emptySet())) <=> (x === emptySet())) by InstFunSchema(Map(x -> x, y -> emptySet()))(ax"extensionalityAxiom")
        val exRhs = andThen(() |- forall(y, in(y, x) <=> in(y, emptySet())) <=> (x === emptySet())) by Restate
    
        have(forall(y, !in(y, x)) |- (forall(y, in(y, x) <=> in(y, emptySet())) <=> (x === emptySet())) /\ forall(y, in(y, x) <=> in(y, emptySet()))) by RightAnd(exLhs, exRhs)
        andThen(forall(y, !in(y, x)) |- (x === emptySet())) by Trivial
    }
    show

    val emptySetIsASubset = makeTHM(
        () |- subset(emptySet(), x)
    ) {
        val lhs = have(() |- subset(emptySet(), x) <=> forall(z, in(z, emptySet()) ==> in(z, x))) by InstFunSchema(Map(x -> emptySet(), y -> x))(ax"subsetAxiom")

        have(() |- !in(y, emptySet())) by InstFunSchema(Map(x -> y))(ax"EmptySet")
        andThen(() |- Set(!in(y, emptySet()), in(y, x))) by Weakening
        andThen(() |- in(y, emptySet()) ==> in(y, x)) by Rewrite
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
        //      and hence is not empty itself

        val lhs = have(() |- in(emptySet(), powerSet(x)) <=> subset(emptySet(), x)) by InstFunSchema(Map(x -> emptySet(), y -> x))(ax"powerAxiom")

        have(() |- (in(emptySet(), powerSet(x)) <=> subset(emptySet(), x)) /\ subset(emptySet(), x)) by RightAnd(lhs, thm"emptySetIsASubset")
        val emptyinPower = andThen(() |- in(emptySet(), powerSet(x))) by Trivial
        val nonEmpty = have(in(emptySet(), powerSet(x)) |- !(powerSet(x) === emptySet())) by InstFunSchema(Map(y -> emptySet(), x -> powerSet(x)))(thm"setWithElementNonEmpty")

        have(() |- !(powerSet(x) === emptySet())) by Cut(emptyinPower, nonEmpty)
    }
    show

    val singletonHasNoExtraElements = makeTHM(
        () |- in(y, singleton(x)) <=> (x === y)
    ) {
        have(() |- in(y, unorderedPair(x, x)) <=> (x === y) \/ (x === y)) by InstFunSchema(Map(x -> x, y -> x, z -> y))(ax"pairAxiom")
        andThen(() |- in(y, singleton(x)) <=> (x === y)) by Restate
    }
    show

    val singletonNonEmpty = makeTHM(
        () |- !(singleton(x) === emptySet())
    ) {
        val reflLhs = have(() |- in(x, singleton(x)) <=> (x === x)) by InstFunSchema(Map(y -> x))(thm"singletonHasNoExtraElements")
        
        val reflRhs = have(() |- (x === x)) by RightRefl
        have(() |- (x === x) /\ (in(x, singleton(x)) <=> (x === x))) by RightAnd(reflLhs, reflRhs)
        val lhs = andThen(() |- in(x, singleton(x))) by Trivial

        val rhs = have(in(x, singleton(x)) |- !(singleton(x) === emptySet())) by InstFunSchema(Map(y -> x, x -> singleton(x)))(thm"setWithElementNonEmpty")
        
        have(() |- !(singleton(x) === emptySet())) by Cut(lhs, rhs)
    }
    show

    // this is imposed by well founded ness of set inclusion
    // expressed by the Axiom of Regularity / Foundation
    val selfNonInclusion = makeTHM(
        () |- !in(x, x)
    ) {
        val X = singleton(x)

        have(() |- !(X === emptySet()) ==> exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))) by InstFunSchema(Map(x -> X))(ax"foundationAxiom")
        val lhs = andThen(!(X === emptySet()) |- exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)))) by Restate

        have(in(y, X) |- in(y, X) <=> (x === y)) by Weakening(thm"singletonHasNoExtraElements")
        val innerRhs = andThen(in(y, X) |- (x === y)) by Trivial

        have(Set(in(x, X), (in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by Hypothesis
        andThen(Set(in(x, X), forall(z, in(z, X) ==> !in(z, x)), in(y, X)) |- in(z, X) ==> !in(z, x)) by LeftForall(z)
        andThen(Set(in(x, X), forall(z, in(z, X) ==> !in(z, x)), in(x, X)) |- in(x, X) ==> !in(x, x)) by InstFunSchema(Map(z -> x, y -> x))
        val coreRhs = andThen(in(x, X) /\ forall(z, in(z, X) ==> !in(z, x)) |- !in(x, x)) by Restate

        // now we need to show that the assumption is indeed true
        // this requires destruction of the existential quantifier in lhs
        have(in(x, X) /\ forall(z, in(z, X) ==> !in(z, x)) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Hypothesis
        val innerRhs2 = andThen(Set(in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)), x === y) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by LeftSubstEq(List((x, y)), lambda(Seq(y), in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))))

        have(Set(in(y, X), in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Cut(innerRhs, innerRhs2)
        andThen(in(y, X) /\ forall(z, in(z, X) ==> !in(z, y)) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by Restate
        val coreLhs = andThen(exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- in(x, X) /\ forall(z, in(z, X) ==> !in(z, x))) by LeftExists

        val rhs = have(exists(y, in(y, X) /\ forall(z, in(z, X) ==> !in(z, y))) |- !in(x, x)) by Cut(coreLhs, coreRhs)

        val finRhs = have(!(X === emptySet()) |- !in(x, x)) by Cut(lhs, rhs)
        val finLhs = have(() |- !(X === emptySet())) by Rewrite(thm"singletonNonEmpty")

        have(() |- !in(x, x)) by Cut(finLhs, finRhs)
    }
    show

    val powerSetNonInclusion = makeTHM(
            Exists(x, properSubset(powerSet(x), x)) |- ()
        ) {
            val lhs = have(subset(powerSet(x), x) |- subset(powerSet(x), x)) by Hypothesis

            val rhs = have(() |- in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x)) by InstFunSchema(Map(x -> powerSet(x), y -> x))(ax"powerAxiom")

            have(subset(powerSet(x), x) |- subset(powerSet(x), x) /\ (in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x))) by RightAnd(lhs, rhs)
            val contraLhs = andThen(subset(powerSet(x), x) |- in(powerSet(x), powerSet(x))) by Trivial

            val contraRhs = have(() |- !in(powerSet(x), powerSet(x))) by InstFunSchema(Map(x -> powerSet(x)))(thm"selfNonInclusion")

            have(subset(powerSet(x), x) |- !in(powerSet(x), powerSet(x)) /\ in(powerSet(x), powerSet(x))) by RightAnd(contraLhs, contraRhs)
            andThen(subset(powerSet(x), x) |- ()) by Restate
            andThen(subset(powerSet(x), x) |- (x === powerSet(x))) by Weakening
            andThen(properSubset(powerSet(x), x) |- ()) by Restate
            andThen(exists(x, properSubset(powerSet(x), x)) |- ()) by LeftExists
    }
    show
}
