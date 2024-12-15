package lisa.maths.topology

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import lisa.automation.kernel.CommonTactics.Definition

import lisa.maths.topology.Topology.*
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.SetTheoryBasics.*
import lisa.automation.kernel.CommonTactics.*

object DiscreteTopology extends lisa.Main {
  import lisa.maths.settheory.SetTheory.*
  // var defs
  private val x, y, z, a, b, c, t = variable
  private val X, T = variable
  private val A, B, Y = variable

  // A discrete Topology is is where T contains all possible subsets of X from Def 1.1.6 in the book
  val discreteTopology = DEF(X, T) --> nonEmpty(X) /\ (T === powerSet(X))

  // Proof that a discrite Topology is actually a topology (satisfies all conditions of a topology)
  val discreteIsTopology = Theorem(
    discreteTopology(X, T) |- topology(X, T)
  ) {
    assume(discreteTopology(X, T))
    val discreteDef = have(nonEmpty(X) /\ (T === powerSet(X))) by Tautology.from(discreteTopology.definition)
    val ext = have(forall(z, in(z, T) <=> in(z, powerSet(X)))) by Tautology.from(extensionalityAxiom of (x := T, y := powerSet(X)), discreteDef)

    val isSub = have(setOfSubsets(X, T)) by Tautology.from(equalityBySubset of (x := T, y := powerSet(X)), discreteDef, setOfSubsets.definition)
    val contEx = have(containsExtremes(X, T)) subproof {
      val a1 = have(in(∅, T) <=> in(∅, powerSet(X))) by InstantiateForall(∅)(ext)
      val a2 = have(∅ ∈ powerSet(X)) by Tautology.from(powerAxiom of (x := ∅, y := X), emptySetIsASubset of (x := X))
      val hasEmpty = have(∅ ∈ T) by Tautology.from(a1, a2)

      have(in(X, T) <=> in(X, powerSet(X))) by InstantiateForall(X)(ext)
      have(X ∈ T) by Tautology.from(lastStep, elemInItsPowerSet of (x := X))
      have(thesis) by Tautology.from(lastStep, hasEmpty, containsExtremes.definition)
    }
    val contUn = have(containsUnion(T)) subproof {
      have((Y ⊆ T) |- (union(Y) ∈ T)) subproof {
        assume(Y ⊆ T)
        have(Y ⊆ powerSet(X)) by Tautology.from(discreteDef, equalityBySubset of (x := T, y := powerSet(X)), subsetTransitivity of (a := Y, b := T, c := powerSet(X)))
        have(union(Y) ∈ powerSet(X)) by Tautology.from(lastStep, subsetClosedUnion of (x := Y, y := X), powerAxiom of (x := union(Y), y := X))
        have(thesis) by Tautology.from(lastStep, discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := union(Y)))
      }
      thenHave((Y ⊆ T) ==> (union(Y) ∈ T)) by Tautology
      thenHave(forall(Y, (Y ⊆ T) ==> (union(Y) ∈ T))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsUnion.definition)
    }
    val contInt = have(containsIntersection(T)) subproof {
      have((A ∈ T, B ∈ T) |- (A ∩ B ∈ T)) subproof {
        assume((A ∈ T), (B ∈ T))
        val first = have(A ⊆ X) by Tautology.from(discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := A), powerAxiom of (x := A, y := X))
        val second = have(B ⊆ X) by Tautology.from(discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := B), powerAxiom of (x := B, y := X))
        have(A ∩ B ∈ powerSet(X)) by Tautology.from(first, second, subsetClosedIntersection of (x := A, y := B, z := X), powerAxiom of (x := A ∩ B, y := X))
        have(thesis) by Tautology.from(lastStep, discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := A ∩ B))
      }
      have((A ∈ T /\ B ∈ T) ==> (A ∩ B ∈ T)) by Tautology.from(lastStep, containsIntersection.definition)
      thenHave(forall(B, (A ∈ T /\ B ∈ T) ==> (A ∩ B ∈ T))) by RightForall
      thenHave(forall(A, forall(B, (A ∈ T /\ B ∈ T) ==> (A ∩ B ∈ T)))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsIntersection.definition)
    }

    have(thesis) by Tautology.from(discreteDef, isSub, contEx, contUn, contInt, topology.definition)
  }

  // A indiscrete Topology is is where T contains only the empty set and X. Therefore the smallest possible topology for a given X. From Def 1.1.6 in the book
  val indiscreteTopology = DEF(X, T) --> nonEmpty(X) /\ (T === unorderedPair(∅, X))

  // proof that the indiscrete Topology is acutally a topology
  val indiscreteIsTopology = Theorem(
    indiscreteTopology(X, T) ==> topology(X, T)
  ) {
    assume(indiscreteTopology(X, T))
    val indiscreteDef = have(nonEmpty(X) /\ (T === unorderedPair(∅, X))) by Tautology.from(indiscreteTopology.definition)
    val emptySubs = have(∅ ∈ powerSet(X)) by Tautology.from(emptySetIsASubset of (x := X), powerAxiom of (x := emptySet, y := X))
    val fullSubs = have(X ∈ powerSet(X)) by Tautology.from(elemInItsPowerSet of (x := X))

    val isSub = have(setOfSubsets(X, T)) subproof {
      have(in(unorderedPair(∅, X), powerSet(powerSet(X)))) by Tautology.from(emptySubs, fullSubs, unorderedPairInPowerSet of (x := powerSet(X), a := emptySet, b := X))
      have(unorderedPair(∅, X) ⊆ powerSet(X)) by Tautology.from(lastStep, powerAxiom of (x := unorderedPair(∅, X), y := powerSet(X)))
      have(thesis) by Tautology.from(lastStep, indiscreteDef, replaceEqualitySubsetLeft of (x := unorderedPair(∅, X), y := T, z := powerSet(X)), setOfSubsets.definition)
    }

    val contEx = have(containsExtremes(X, T)) subproof {
      val a = have(X ∈ T) by Tautology.from(pairAxiom of (x := emptySet, y := X, z := X), indiscreteDef, replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := X))
      val b = have(∅ ∈ T) by Tautology.from(
        pairAxiom of (x := emptySet, y := X, z := emptySet),
        indiscreteDef,
        replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := emptySet)
      )
      have(thesis) by Tautology.from(a, b, containsExtremes.definition)
    }

    val contUn = have(containsUnion(T)) subproof {
      have((Y ⊆ T) |- union(Y) ∈ T) subproof {
        assume(Y ⊆ T)
        have(Y ⊆ unorderedPair(∅, X)) by Tautology.from(indiscreteDef, replaceEqualitySubsetRight of (x := T, y := unorderedPair(∅, X), z := Y))
        have(forall(z, in(z, Y) ==> in(z, unorderedPair(∅, X)))) by Tautology.from(lastStep, subsetAxiom of (x := Y, y := unorderedPair(∅, X)))
        thenHave(in(z, Y) ==> in(z, unorderedPair(∅, X))) by InstantiateForall(z)
        have(in(z, Y) |- ((z === ∅) \/ (z === X))) by Tautology.from(lastStep, pairAxiom of (x := emptySet, y := X))
        thenHave((in(z, Y) /\ in(a, z)) |- (((z === ∅) \/ (z === X)) /\ in(a, z))) by Tautology
        thenHave((in(z, Y) /\ in(a, z)) |- ((((z === ∅) /\ in(a, z))) \/ ((z === X) /\ in(a, z)))) by Tautology
        have((in(z, Y) /\ in(a, z)) |- (in(a, ∅) \/ (in(a, X) /\ (z === X)))) by Tautology.from(
          lastStep,
          replaceEqualityContainsRight of (x := z, y := emptySet, z := a),
          replaceEqualityContainsRight of (x := z, y := X, z := a)
        )
        have((in(z, Y) /\ in(a, z)) |- (in(a, X) /\ (z === X) /\ in(z, Y))) by Tautology.from(lastStep, emptySetAxiom of (x := a))
        have((in(z, Y) /\ in(a, z)) |- (in(a, X) /\ in(X, Y))) by Tautology.from(lastStep, replaceEqualityContainsLeft of (x := z, y := X, z := Y))
        thenHave(exists(z, in(z, Y) /\ in(a, z)) |- (in(a, X) /\ in(X, Y))) by LeftExists
        val before = have(in(a, union(Y)) ==> (in(a, X) /\ in(X, Y))) by Tautology.from(lastStep, unionAxiom of (z := a, x := Y, y := z), emptySetAxiom of (x := a))
        thenHave(in(a, union(Y)) ==> in(a, X)) by Tautology
        val base = thenHave(forall(a, in(a, union(Y)) ==> in(a, X))) by RightForall
        val cond1 = have(forall(a, !in(a, union(Y))) |- union(Y) === ∅) by Tautology.from(setWithNoElementsIsEmpty of (y := a, x := union(Y)))
        val cond2 = have(exists(a, in(a, union(Y))) |- union(Y) === X) subproof {
          val unionGrow = have(in(a, union(Y)) |- (X ⊆ union(Y))) by Tautology.from(before, unionDoesntShrink of (x := X, y := Y))
          have(in(a, union(Y)) |- (union(Y) === X)) by Tautology.from(base, unionGrow, subsetAxiom of (x := union(Y), y := X, z := a), equalityBySubset of (x := union(Y), y := X))
          thenHave(thesis) by LeftExists
        }
        have((union(Y) === ∅) \/ (union(Y) === X)) by Tautology.from(base, cond1, cond2)
        have(union(Y) ∈ unorderedPair(∅, X)) by Tautology.from(lastStep, pairAxiom of (x := emptySet, y := X, z := union(Y)))
        have(thesis) by Tautology.from(lastStep, indiscreteDef, replaceEqualityContainsRight of (x := unorderedPair(∅, X), y := T, z := union(Y)))
      }
      thenHave((Y ⊆ T) ==> (union(Y) ∈ T)) by Tautology
      thenHave(forall(Y, (Y ⊆ T) ==> (union(Y) ∈ T))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsUnion.definition)
    }

    val contInt = have(containsIntersection(T)) subproof {
      have((A ∈ T /\ B ∈ T) |- (A ∩ B ∈ T)) subproof {
        assume((A ∈ T /\ B ∈ T))
        have(A ∈ unorderedPair(∅, X) /\ B ∈ unorderedPair(∅, X)) by Tautology.from(
          indiscreteDef,
          replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := A),
          replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := B)
        )
        val allPossibilities =
          have(((A === ∅) \/ (A === X)) /\ ((B === ∅) \/ (B === X))) by Tautology.from(lastStep, pairAxiom of (x := emptySet, y := X, z := A), pairAxiom of (x := emptySet, y := X, z := B))
        val aEmpty = have((A === ∅) |- (A ∩ B) === ∅) subproof {
          assume(A === emptySet)
          have(in(t, setIntersection(A, B)) <=> (in(t, A) /\ in(t, B))) by Tautology.from(setIntersectionMembership of (x := A, y := B))
          have(!in(t, setIntersection(A, B))) by Tautology.from(lastStep, replaceEqualityContainsRight of (x := emptySet, y := A, z := t), emptySetAxiom of (x := t))
          thenHave(forall(t, !in(t, setIntersection(A, B)))) by RightForall
          have(thesis) by Tautology.from(lastStep, setWithNoElementsIsEmpty of (y := t, x := setIntersection(A, B)))
        }
        val oneEmpty = have(((A === ∅) \/ (B === ∅)) |- ((A ∩ B) === ∅)) by Tautology.from(
          aEmpty,
          aEmpty of (A := B, B := A),
          setIntersectionCommutativity of (x := A, y := B),
          equalityTransitivity of (x := setIntersection(A, B), y := setIntersection(B, A), z := emptySet)
        )
        val bothFull = have((A === X, B === X) |- A ∩ B === X) subproof {
          assume(((A === X) /\ (B === X)))
          have(in(t, setIntersection(A, B)) <=> (in(t, A) /\ in(t, B))) by Tautology.from(setIntersectionMembership of (x := A, y := B))
          have(in(t, setIntersection(A, B)) <=> in(t, X)) by Tautology.from(
            lastStep,
            replaceEqualityContainsRight of (x := X, y := A, z := t),
            replaceEqualityContainsRight of (x := X, y := B, z := t)
          )
          thenHave(forall(t, in(t, setIntersection(A, B)) <=> in(t, X))) by RightForall
          have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x := setIntersection(A, B), y := X, z := t))
        }
        have((A ∩ B === ∅) \/ (A ∩ B === X)) by Tautology.from(allPossibilities, oneEmpty, bothFull)
        have(in(A ∩ B, unorderedPair(∅, X))) by Tautology.from(lastStep, pairAxiom of (z := setIntersection(A, B), x := emptySet, y := X))
        have(thesis) by Tautology.from(lastStep, indiscreteDef, replaceEqualityContainsRight of (x := unorderedPair(∅, X), y := T, z := setIntersection(A, B)))
      }
      thenHave((A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T) by Tautology
      thenHave(forall(B, (A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T)) by RightForall
      thenHave(forall(A, forall(B, (A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsIntersection.definition)
    }

    have(thesis) by Tautology.from(indiscreteDef, isSub, contEx, contUn, contInt, topology.definition)
  }

}
