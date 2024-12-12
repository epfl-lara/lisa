package lisa.maths.topology

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import lisa.automation.kernel.CommonTactics.Definition

import lisa.maths.topology.Topology.*
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.SetTheoryBasics.*

object Intersection extends lisa.Main {
  // var defs
  private val x, y, z, a, b, c, t, p = variable
  private val X, T, T1, T2 = variable
  private val S, A, B, Y = variable

  // Proof that the intersection over two topologies defined over the same set X is also a topology
  val intersectionIsTopology = Theorem(
    (topology(X, T1) /\ topology(X, T2)) |- topology(X, T1 ∩ T2)
  ) {
    assume(topology(X, T1) /\ topology(X, T2))
    val topo1 = have(nonEmpty(X) /\ setOfSubsets(X, T1) /\ containsExtremes(X, T1) /\ containsUnion(T1) /\ containsIntersection(T1)) by Tautology.from(topology.definition of (T := T1))
    val topo2 = have(nonEmpty(X) /\ setOfSubsets(X, T2) /\ containsExtremes(X, T2) /\ containsUnion(T2) /\ containsIntersection(T2)) by Tautology.from(topology.definition of (T := T2))

    val nonEm = have(nonEmpty(X)) by Tautology.from(topo1)

    val isSub = have(setOfSubsets(X, T1 ∩ T2)) by Tautology.from(
      subsetClosedIntersection of (x := T1, y := T2, z := powerSet(X)),
      topo1,
      topo2,
      setOfSubsets.definition of (T := T1 ∩ T2),
      setOfSubsets.definition of (T := T1),
      setOfSubsets.definition of (T := T2)
    )
    val contEx = have(containsExtremes(X, T1 ∩ T2)) subproof {
      val empty = have(∅ ∈ (T1 ∩ T2)) by Tautology.from(
        setIntersectionMembership of (t := emptySet, x := T1, y := T2),
        containsExtremes.definition of (T := T1),
        containsExtremes.definition of (T := T2),
        topo1,
        topo2
      )
      val full = have(X ∈ (T1 ∩ T2)) by Tautology.from(
        setIntersectionMembership of (t := X, x := T1, y := T2),
        containsExtremes.definition of (T := T1),
        containsExtremes.definition of (T := T2),
        topo1,
        topo2
      )
      have(thesis) by Tautology.from(empty, full, containsExtremes.definition of (T := T1 ∩ T2))
    }
    val contUn = have(containsUnion(T1 ∩ T2)) subproof {
      have(forall(Y, (Y ⊆ T1) ==> (union(Y) ∈ T1))) by Tautology.from(topo1, containsUnion.definition of (T := T1))
      val t1 = thenHave((Y ⊆ T1) ==> (union(Y) ∈ T1)) by InstantiateForall(Y)
      have(forall(Y, (Y ⊆ T2) ==> (union(Y) ∈ T2))) by Tautology.from(topo2, containsUnion.definition of (T := T2))
      val t2 = thenHave((Y ⊆ T2) ==> (union(Y) ∈ T2)) by InstantiateForall(Y)
      have((Y ⊆ (T1 ∩ T2)) ==> (union(Y) ∈ (T1 ∩ T2))) subproof {
        assume(Y ⊆ (T1 ∩ T2))
        val leadsUnion = have((containsUnion(T), Y ⊆ T) |- union(Y) ∈ T) subproof {
          assume(containsUnion(T))
          have(forall(Y, (Y ⊆ T) ==> (union(Y) ∈ T))) by Tautology.from(containsUnion.definition)
          thenHave((Y ⊆ T) ==> (union(Y) ∈ T)) by InstantiateForall(Y)
          thenHave(thesis) by Tautology
        }
        have((Y ⊆ T1) /\ (Y ⊆ T2)) by Tautology.from(subsetUnderIntersection of (x := T1, y := T2, z := Y))
        have(union(Y) ∈ T1 /\ union(Y) ∈ T2) by Tautology.from(leadsUnion of (T := T1), leadsUnion of (T := T2), lastStep, topo1, topo2)
        have(thesis) by Tautology.from(lastStep, setIntersectionMembership of (x := T1, y := T2, t := union(Y)))
      }
      thenHave(forall(Y, (Y ⊆ (T1 ∩ T2)) ==> (union(Y) ∈ (T1 ∩ T2)))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsUnion.definition of (T := T1 ∩ T2))
    }
    val contInt = have(containsIntersection(T1 ∩ T2)) subproof {
      have((A ∈ (T1 ∩ T2) /\ B ∈ (T1 ∩ T2)) ==> A ∩ B ∈ (T1 ∩ T2)) subproof {
        assume(A ∈ (T1 ∩ T2) /\ B ∈ (T1 ∩ T2))
        val leadsInt = have((containsIntersection(T), (A ∈ T /\ B ∈ T)) |- (A ∩ B ∈ T)) subproof {
          assume(containsIntersection(T))
          have(forall(A, forall(B, (A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T))) by Tautology.from(containsIntersection.definition)
          thenHave(forall(B, (A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T)) by InstantiateForall(A)
          thenHave((A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T) by InstantiateForall(B)
          thenHave(thesis) by Tautology
        }
        have(A ∈ T1 /\ A ∈ T2 /\ B ∈ T1 /\ B ∈ T2) by Tautology.from(setIntersectionMembership of (t := A, x := T1, y := T2), setIntersectionMembership of (t := B, x := T1, y := T2))
        have(A ∩ B ∈ T1 /\ A ∩ B ∈ T2) by Tautology.from(lastStep, leadsInt of (T := T1), leadsInt of (T := T2), topo1, topo2)
        have(thesis) by Tautology.from(lastStep, setIntersectionMembership of (t := A ∩ B, x := T1, y := T2))
      }
      thenHave(forall(B, (A ∈ (T1 ∩ T2) /\ B ∈ (T1 ∩ T2)) ==> A ∩ B ∈ (T1 ∩ T2))) by RightForall
      thenHave(forall(A, forall(B, (A ∈ (T1 ∩ T2) /\ B ∈ (T1 ∩ T2)) ==> A ∩ B ∈ (T1 ∩ T2)))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsIntersection.definition of (T := T1 ∩ T2))
    }
    have(thesis) by Tautology.from(nonEm, isSub, contEx, contUn, contInt, topology.definition of (T := T1 ∩ T2))
  }
}
