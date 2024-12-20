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

  /*
    Theorem: Equality by Subset
    x is equal to y iff x ⊆ y and y ⊆ x
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

  /*
    Theorem: Equality replaces contains right side
    if x is equal to y then we have z ∈ x iff z ∈ y for any z
   */
  val replaceEqualityContainsRight = Theorem((x === y) ==> ((z ∈ x) <=> (z ∈ y))) {
    have((x === y) |- ((z ∈ x) <=> (z ∈ y))) subproof {
      assume(x === y)
      have(forall(z, (z ∈ x) <=> (z ∈ y))) by Tautology.from(extensionalityAxiom)
      thenHave(thesis) by InstantiateForall(z)
    }
    thenHave(thesis) by Tautology
  }

  /*
    Theorem: Equality replaces contains left side
    if x is equal to y then we have x ∈ z iff y ∈ z for any z
   */
  val replaceEqualityContainsLeft = Theorem((x === y) ==> ((x ∈ z) <=> (y ∈ z))) {
    have(((x === y), (y ∈ z)) |- (x ∈ z)) subproof {
      have((y ∈ z, (x === y)) |- (y ∈ z)) by Tautology
      thenHave(thesis) by RightSubstEq.withParametersSimple(List((y, x)), lambda(x, in(x, z)))
    }
    have(thesis) by Tautology.from(lastStep, lastStep of (x := y, y := x))
  }

  /*
    Theorem: Equality replaces subset right side
    if x is equal to y then we have z ⊆ x iff z ⊆ y for any z
   */
  val replaceEqualitySubsetRight = Theorem((x === y) ==> ((z ⊆ x) <=> (z ⊆ y))) {
    val side = have(((x === y), (z ⊆ x)) |- (z ⊆ y)) subproof {
      assume((x === y) /\ (z ⊆ x))
      have(thesis) by Tautology.from(equalityBySubset, subsetTransitivity of (a := z, b := x, c := y))
    }
    have(thesis) by Tautology.from(side, side of (x := y, y := x))
  }

  /*
    Theorem: Equality replaces subset left side
    if x is equal to y then we have x ⊆ z iff y ⊆ z for any z
   */
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

  /*
    Theorem: Subset is closed under intersection
    if x ⊆ z and y ⊆ z we have x ∩ y ⊆ z
   */
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

  /*
    Theorem: Intersection means subset of both elements
    if z ⊆ x ∩ y we know z ⊆ x and z ⊆ y
   */
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

  /*
    Theorem: Subset is closed under setUnion
    if x ⊆ z and y ⊆ z we have x u y ⊆ z
   */
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

  /*
    Theorem: Subset is closed under union
    The union of any (finite or infinite) number of sets in y is still in y
    if x ⊆ powerSet(y) we have union(x) ⊆ y
   */
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

  /*
    Theorem: Union doesnt shrink
    The union of any (finite or infinite) number of sets where one set is x has to include x
    if x ∈ y we have x ⊆ unnion(y)
   */
  val unionDoesntShrink = Theorem((x ∈ y) |- (x ⊆ union(y))) {
    assume(in(x, y))
    thenHave(in(z, x) |- (in(z, x) /\ in(x, y))) by Tautology
    thenHave(in(z, x) |- exists(x, in(z, x) /\ in(x, y))) by RightExists
    have(in(z, x) ==> in(z, union(y))) by Tautology.from(lastStep, unionAxiom of (x := y, y := x))
    thenHave(forall(z, in(z, x) ==> in(z, union(y)))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := x, y := union(y)))
  }

  /*
    Theorem: Subset propagates over elementOf
    if z ∈ x and x ⊆ y we have z ∈ y
   */
  val subsetTactic = Theorem((x ⊆ y, z ∈ x) |- z ∈ y) {
    assume(x ⊆ y, z ∈ x)

    have(forall(z, z ∈ x ==> z ∈ y)) by Tautology.from(subsetAxiom)
    thenHave(z ∈ x ==> z ∈ y) by InstantiateForall(z)
    thenHave(thesis) by Tautology
  }

  /*
    Theorem: Difference shrinks
    x \ y ⊆ x
   */
  val differenceShrinks = Theorem(setDifference(x, y) ⊆ x) {
    have(in(z, setDifference(x, y)) ==> in(z, x)) by Tautology.from(setDifferenceMembership of (t := z))
    thenHave(forall(z, in(z, setDifference(x, y)) ==> in(z, x))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := setDifference(x, y), y := x))
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

  val equalityReflexivity = Theorem(x === x) {
    have(thesis) by Tautology.from(equalityBySubset of (x := x, y := x))
  }
}
