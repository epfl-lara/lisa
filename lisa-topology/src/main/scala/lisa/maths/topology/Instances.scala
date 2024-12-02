package lisa.maths.topology

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import lisa.automation.kernel.CommonTactics.Definition

import lisa.maths.topology.Topology.*
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory._

object Instances extends lisa.Main {
  // var defs
  private val x, y, z = variable
  private val X, T = variable
  private val S, A, B, Y = variable

  val discreteTopology = DEF(X, T) --> nonEmpty(X) /\ (T === powerSet(X))
  val indiscreteTopology = DEF(X, T) --> nonEmpty(X) /\ (T === unorderedPair(∅, X))

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

      val b1 = have(in(X, T) <=> in(X, powerSet(X))) by InstantiateForall(X)(ext)
      val hasFull = have(X ∈ T) by Tautology.from(elemInItsPowerSet of (x := X), b1)
      have(thesis) by Tautology.from(hasEmpty, hasFull, containsExtremes.definition)
    }
    val contUn = have(containsUnion(T)) subproof {
      have(Y ⊆ T |- union(Y) ∈ T) subproof {
        assume(Y ⊆ T)
        have(Y ⊆ powerSet(X)) by Tautology.from(subsetTransitivity of (a := Y, b := T, c := powerSet(X)), isSub, setOfSubsets.definition)

        have(in(z, union(Y)) |- in(z, X)) subproof {
          assume(in(z, union(Y)))
          have(exists(y, in(y, Y) /\ in(z, y))) by Tautology.from(unionAxiom of (x := Y))
        }

        // forall(z, in(z, union(Y)) ==> in(z, X))
        // in(z, union(Y)) <=> exists(y, in(y, Y) /\ in(z, y))
        sorry
      }
    }
    val contInt = have(containsIntersection(T)) subproof {
      val sub = have(A ∈ T, B ∈ T |- A ∩ B ∈ T) subproof {
        assume((A ∈ T), (B ∈ T))

      }
    }
    sorry
    /*
    have(thesis) by Tautology.from(nonE, subset, contEx, contUn, contInt)
     */
  }

  val indiscreteIsTopology = Theorem(
    indiscreteTopology(X, T) ==> topology(X, T)
  ) {
    sorry
  }
}
