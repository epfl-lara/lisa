package lisa.maths.settheory

import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.functions.Functionals.*

import scala.collection.immutable.{Map => ScalaMap}
import lisa.maths.settheory.SetTheory.relationDomain

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
  private val f = variable
  private val r = variable

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

  val subsetTactic = Theorem((x ⊆ y, z ∈ x) |- z ∈ y) {
    assume(x ⊆ y, z ∈ x)

    have(forall(z, z ∈ x ==> z ∈ y)) by Tautology.from(subsetAxiom)
    thenHave(z ∈ x ==> z ∈ y) by InstantiateForall(z)
    thenHave(thesis) by Tautology
  }

  /**
   * Lemma --- Range introduction and elimination rules. If en element is in the image of a function, then it has a preimage inside its domain.
   *
   *     `functional(f) |- y ⊆ Im(f) <=> ∃x ∈ Dom(f). f(x) = y`
   */
  val functionRangeMembership = Lemma(functional(f) |- in(y, relationRange(f)) <=> ∃(x, in(x, relationDomain(f)) /\ (app(f, x) === y))) {
    assume(functional(f))

    have(forall(y, y ∈ relationRange(f) <=> ∃(x, in(pair(x, y), f)))) by InstantiateForall(relationRange(f))(relationRange.definition of (r := f))
    val defRange = thenHave(y ∈ relationRange(f) <=> ∃(x, in(pair(x, y), f))) by InstantiateForall(y)

    have(∀(x, x ∈ relationDomain(f) <=> ∃(y, pair(x, y) ∈ f))) by InstantiateForall(relationDomain(f))(relationDomain.definition of (r := f))
    val defDomain = thenHave(x ∈ relationDomain(f) <=> ∃(y, pair(x, y) ∈ f)) by InstantiateForall(x)

    val forward = have(y ∈ relationRange(f) ==> ∃(x, in(x, relationDomain(f)) /\ (app(f, x) === y))) subproof {
      assume(y ∈ relationRange(f))
      have(pair(x, y) ∈ f |- pair(x, y) ∈ f) by Tautology
      thenHave(pair(x, y) ∈ f |- ∃(y, pair(x, y) ∈ f)) by RightExists
      have(pair(x, y) ∈ f |- x ∈ relationDomain(f) /\ (app(f, x) === y)) by Tautology.from(
        lastStep,
        pairInFunctionIsApp of (a := x, b := y),
        defDomain
      )
      thenHave(in(pair(x, y), f) |- ∃(x, x ∈ relationDomain(f) /\ (app(f, x) === y))) by RightExists
      thenHave(∃(x, in(pair(x, y), f)) |- ∃(x, x ∈ relationDomain(f) /\ (app(f, x) === y))) by LeftExists
      have(thesis) by Tautology.from(lastStep, defRange)
    }

    val backward = have(∃(x, in(x, relationDomain(f)) /\ (app(f, x) === y)) |- y ∈ relationRange(f)) subproof {
      have(in(x, relationDomain(f)) /\ (app(f, x) === y) |- pair(x, y) ∈ f) by Tautology.from(pairInFunctionIsApp of (a := x, b := y))
      thenHave(in(x, relationDomain(f)) /\ (app(f, x) === y) |- ∃(x, pair(x, y) ∈ f)) by RightExists
      have(in(x, relationDomain(f)) /\ (app(f, x) === y) |- y ∈ relationRange(f)) by Tautology.from(
        lastStep,
        defRange
      )
      thenHave(thesis) by LeftExists
    }

    have(thesis) by Tautology.from(forward, backward)
  }

  val equalitySymmetry = Theorem(
    x === y |- y === x
  ) {
    have(thesis) by Tautology.from(equalityBySubset, equalityBySubset of (x := y, y := x))
  }
}
