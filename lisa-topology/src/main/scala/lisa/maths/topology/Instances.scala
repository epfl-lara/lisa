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

    val isSub = have(setOfSubsets(X, T)) subproof {
      val a = have(in(S, T) <=> in(S, powerSet(X))) by InstantiateForall(S)(ext)
      val b = have(in(S, T) ==> subset(S, X)) by Tautology.from(a, powerAxiom of (x := S, y := X))
      val c = thenHave(forall(S, in(S, T) ==> subset(S, X))) by RightForall
      have(thesis) by Tautology.from(c, setOfSubsets.definition)
    }
    val contEx = have(containsExtremes(X, T)) subproof {
      val a1 = have(in(∅, T) <=> in(∅, powerSet(X))) by InstantiateForall(∅)(ext)
      val a2 = have(∅ ∈ powerSet(X)) by Tautology.from(powerAxiom of (x := ∅, y := X), emptySetIsASubset of (x := X))
      val hasEmpty = have(∅ ∈ T) by Tautology.from(a1, a2)

      val b1 = have(in(X, T) <=> in(X, powerSet(X))) by InstantiateForall(X)(ext)
      val hasFull = have(X ∈ T) by Tautology.from(elemInItsPowerSet of (x := X), b1)
      have(thesis) by Tautology.from(hasEmpty, hasFull, containsExtremes.definition)
    }
    val contUn = have(containsUnion(T)) subproof {
      val a1 = have(in(Y, powerSet(T)) |- (union(Y) ∈ T)) subproof {
        sorry
      }
      val a2 = have(in(Y, powerSet(T)) ==> (union(Y) ∈ T)) by Tautology.from(a1)
      val a3 = thenHave(forall(Y, in(Y, powerSet(T)) ==> (union(Y) ∈ T))) by RightForall
      have(thesis) by Tautology.from(a3, containsUnion.definition)
      /*val a1 = have(powerSet(T) === powerSet(powerSet(X))) by Tautology.from(discreteDef)
      val a2 = have(forall(z, z ∈ powerSet(T) ==> z ∈ powerSet(powerSet(X)))) by Tautology.from(a1, extensionalityAxiom of (y := powerSet(powerSet(X)), x := powerSet(T)))
      val a3 = thenHave(Y ∈ powerSet(T) ==> Y ∈ powerSet(powerSet(X))) by InstantiateForall(Y)
      val a4 = have(Y ∈ powerSet(powerSet(X)) <=> forall(z, in(z, Y) ==> in(z, powerSet(X)))) by Tautology.from(powerAxiom of (x := Y, y := powerSet(X)), subsetAxiom of (x := Y, y := powerSet(X)))*/
    }
    sorry
    /*
    val contInt = have(containsIntersection(T))
    have(thesis) by Tautology.from(nonE, subset, contEx, contUn, contInt)
     */
  }

  val indiscreteIsTopology = Theorem(
    indiscreteTopology(X, T) ==> topology(X, T)
  ) {
    sorry
  }
}
