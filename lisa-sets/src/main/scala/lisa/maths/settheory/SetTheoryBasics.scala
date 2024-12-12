package lisa.maths.settheory

import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*

import scala.collection.immutable.{Map => ScalaMap}

object SetTheoryBasics extends lisa.Main {

  // var defs
  private val x = variable
  private val y = variable
  private val z = variable
  private val w = variable
  private val a = variable
  private val b = variable
  private val c = variable
  private val d = variable
  private val t = variable

  /**
   * Theorems about basic sets
   */

  val equalityBySubset = Theorem((x === y) <=> (x ⊆ y /\ y ⊆ x)) {
    val forward = have(x === y |- x ⊆ y /\ y ⊆ x) subproof {
      assume(x === y)
      have(forall(z, in(z, x) <=> in(z, y))) by Tautology.from(extensionalityAxiom)
      val bothDirections = thenHave(in(z, x) <=> in(z, y)) by InstantiateForall(z)
      thenHave(in(z, x) ==> in(z, y)) by Weakening
      thenHave(forall(z, in(z, x) ==> in(z, y))) by RightForall
      val leftSubset = have(x ⊆ y) by Tautology.from(lastStep, subsetAxiom)
      have(in(z, y) ==> in(z, x)) by Weakening(bothDirections)
      thenHave(forall(z, in(z, y) ==> in(z, x))) by RightForall
      val rightSubset = have(y ⊆ x) by Tautology.from(lastStep, subsetAxiom of (x := y, y := x))
      have(thesis) by Tautology.from(leftSubset, rightSubset)
    }
    val backward = have((x ⊆ y /\ y ⊆ x) |- x === y) subproof {
      assume((x ⊆ y), (y ⊆ x))
      have(forall(z, in(z, x) ==> in(z, y))) by Tautology.from(subsetAxiom)
      val left = thenHave(in(z, x) ==> in(z, y)) by InstantiateForall(z)
      have(forall(z, in(z, y) ==> in(z, x))) by Tautology.from(subsetAxiom of (x := y, y := x))
      val right = thenHave(in(z, y) ==> in(z, x)) by InstantiateForall(z)
      have(in(z, x) <=> in(z, y)) by Tautology.from(left, right)
      val equalityDef = thenHave(forall(z, in(z, x) <=> in(z, y))) by RightForall
      have(thesis) by Tautology.from(equalityDef, extensionalityAxiom)
    }
    have(thesis) by Tautology.from(forward, backward)
  }

  val replaceEqualityContainsRight = Theorem((x === y) ==> ((z ∈ x) <=> (z ∈ y))) {
    have((x === y) |- ((z ∈ x) <=> (z ∈ y))) subproof {
      assume(x === y)
      have(forall(z, (z ∈ x) <=> (z ∈ y))) by Tautology.from(extensionalityAxiom)
      thenHave(thesis) by InstantiateForall(z)
    }
    thenHave(thesis) by Tautology
  }

  val replaceEqualityContainsLeft = Theorem((x === y) ==> ((x ∈ z) <=> (y ∈ z))) {
    have(((x === y), (y ∈ z)) |- (x ∈ z)) subproof {
      have((y ∈ z, (x === y)) |- (y ∈ z)) by Tautology
      thenHave(thesis) by RightSubstEq.withParametersSimple(List((y, x)), lambda(x, in(x, z)))
    }
    have(thesis) by Tautology.from(lastStep, lastStep of (x := y, y := x))
  }

  val replaceEqualitySubsetRight = Theorem((x === y) ==> ((z ⊆ x) <=> (z ⊆ y))) {
    val side = have(((x === y), (z ⊆ x)) |- (z ⊆ y)) subproof {
      assume((x === y) /\ (z ⊆ x))
      have(thesis) by Tautology.from(equalityBySubset, subsetTransitivity of (a := z, b := x, c := y))
    }
    have(thesis) by Tautology.from(side, side of (x := y, y := x))
  }

  val replaceEqualitySubsetLeft = Theorem((x === y) ==> ((x ⊆ z) <=> (y ⊆ z))) {
    val side = have(((x === y), (x ⊆ z)) |- (y ⊆ z)) subproof {
      assume((x === y) /\ (x ⊆ z))
      have(forall(w, in(w, x) ==> in(w, z))) by Tautology.from(subsetAxiom of (y := z, z := w))
      thenHave(in(w, x) ==> in(w, z)) by InstantiateForall(w)
      have(in(w, y) ==> in(w, z)) by Tautology.from(lastStep, replaceEqualityContainsRight of (z := w))
      thenHave(forall(w, in(w, y) ==> in(w, z))) by RightForall
      have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := y, y := z))
    }
    have(thesis) by Tautology.from(side, side of (x := y, y := x))
  }

  val subsetClosedIntersection = Theorem((x ⊆ z, y ⊆ z) |- (x ∩ y) ⊆ z) {
    assume(x ⊆ z, y ⊆ z)
    have(forall(t, in(t, x) ==> in(t, z))) by Tautology.from(subsetAxiom of (y := z, z := t))
    val first = thenHave(in(t, x) ==> in(t, z)) by InstantiateForall(t)

    have(forall(t, in(t, y) ==> in(t, z))) by Tautology.from(subsetAxiom of (x := y, y := z, z := t))
    val second = thenHave(in(t, y) ==> in(t, z)) by InstantiateForall(t)

    have(in(t, setIntersection(x, y)) ==> in(t, z)) by Tautology.from(first, second, setIntersectionMembership)
    thenHave(forall(t, in(t, setIntersection(x, y)) ==> in(t, z))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := setIntersection(x, y), y := z))
  }

  val subsetUnderIntersection = Theorem((z ⊆ (x ∩ y)) |- (z ⊆ x /\ z ⊆ y)) {
    assume(z ⊆ (x ∩ y))
    have(forall(t, in(t, z) ==> in(t, x ∩ y))) by Tautology.from(subsetAxiom of (x := z, y := x ∩ y, z := t))
    thenHave(in(t, z) ==> in(t, x ∩ y)) by InstantiateForall(t)
    val both = have((in(t, z) ==> in(t, x)) /\ (in(t, z) ==> in(t, y))) by Tautology.from(lastStep, setIntersectionMembership of (x := x, y := y))
    have(in(t, z) ==> in(t, x)) by Weakening(both)
    thenHave(forall(t, in(t, z) ==> in(t, x))) by RightForall
    val first = have(z ⊆ x) by Tautology.from(lastStep, subsetAxiom of (x := z, y := x, z := t))
    have(in(t, z) ==> in(t, y)) by Weakening(both)
    thenHave(forall(t, in(t, z) ==> in(t, y))) by RightForall
    val second = have(z ⊆ y) by Tautology.from(lastStep, subsetAxiom of (x := z, y := y, z := t))
    have(thesis) by Tautology.from(first, second)
  }

  val subsetClosedSetUnion = Theorem((x ⊆ z, y ⊆ z) |- setUnion(x, y) ⊆ z) {
    assume(x ⊆ z, y ⊆ z)
    have(forall(t, in(t, x) ==> in(t, z))) by Tautology.from(subsetAxiom of (y := z, z := t))
    val first = thenHave(in(t, x) ==> in(t, z)) by InstantiateForall(t)

    have(forall(t, in(t, y) ==> in(t, z))) by Tautology.from(subsetAxiom of (x := y, y := z, z := t))
    val second = thenHave(in(t, y) ==> in(t, z)) by InstantiateForall(t)

    have(in(t, setUnion(x, y)) ==> in(t, z)) by Tautology.from(first, second, setUnionMembership of (z := t))
    thenHave(forall(t, in(t, setUnion(x, y)) ==> in(t, z))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := setUnion(x, y), y := z))
  }

  val subsetClosedUnion = Theorem((x ⊆ powerSet(y)) |- union(x) ⊆ y) {
    assume(x ⊆ powerSet(y))
    have(forall(z, in(z, x) ==> in(z, powerSet(y)))) by Tautology.from(subsetAxiom of (y := powerSet(y)))
    thenHave(in(z, x) ==> in(z, powerSet(y))) by InstantiateForall(z)
    have(in(z, x) |- forall(w, in(w, z) ==> in(w, y))) by Tautology.from(lastStep, powerAxiom of (x := z), subsetAxiom of (x := z, z := w))
    thenHave(in(z, x) |- (in(w, z) ==> in(w, y))) by InstantiateForall(w)
    have((in(z, x) /\ in(w, z)) |- in(w, y)) by Tautology.from(lastStep)
    thenHave(exists(z, in(z, x) /\ in(w, z)) |- in(w, y)) by LeftExists
    have(in(w, union(x)) ==> in(w, y)) by Tautology.from(lastStep, unionAxiom of (z := w, y := z))
    thenHave(forall(w, in(w, union(x)) ==> in(w, y))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := union(x)))
  }

  val unionDoesntShrink = Theorem((x ∈ y) |- (x ⊆ union(y))) {
    assume(in(x, y))
    thenHave(in(z, x) |- (in(z, x) /\ in(x, y))) by Tautology
    thenHave(in(z, x) |- exists(x, in(z, x) /\ in(x, y))) by RightExists
    have(in(z, x) ==> in(z, union(y))) by Tautology.from(lastStep, unionAxiom of (x := y, y := x))
    thenHave(forall(z, in(z, x) ==> in(z, union(y)))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := x, y := union(y)))
  }

}
