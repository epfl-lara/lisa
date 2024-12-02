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
      val leftForall = thenHave(forall(z, in(z, x) ==> in(z, y))) by RightForall
      val leftSubset = have(x ⊆ y) by Tautology.from(leftForall, subsetAxiom)
      have(in(z, y) ==> in(z, x)) by Weakening(bothDirections)
      val rightForall = thenHave(forall(z, in(z, y) ==> in(z, x))) by RightForall
      val rightSubset = have(y ⊆ x) by Tautology.from(rightForall, subsetAxiom of (x := y, y := x))
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

  val subsetClosedIntersection = Theorem((x ⊆ z, y ⊆ z) |- (x ∩ y) ⊆ z) {
    assume(x ⊆ z, y ⊆ z)
    have(forall(t, in(t, x) ==> in(t, z))) by Tautology.from(subsetAxiom of (y := z, z := t))
    val first = thenHave(in(t, x) ==> in(t, z)) by InstantiateForall(t)

    have(forall(t, in(t, y) ==> in(t, z))) by Tautology.from(subsetAxiom of (x := y, y := z, z := t))
    val second = thenHave(in(t, y) ==> in(t, z)) by InstantiateForall(t)

    have(in(t, setIntersection(x, y)) ==> in(t, z)) by Tautology.from(first, second, setIntersectionMembership)
    val defSubs = thenHave(forall(t, in(t, setIntersection(x, y)) ==> in(t, z))) by RightForall
    have(thesis) by Tautology.from(defSubs, subsetAxiom of (x := setIntersection(x, y), y := z))
  }

  val subsetClosedSetUnion = Theorem((x ⊆ z, y ⊆ z) |- setUnion(x, y) ⊆ z) {
    assume(x ⊆ z, y ⊆ z)
    have(forall(t, in(t, x) ==> in(t, z))) by Tautology.from(subsetAxiom of (y := z, z := t))
    val first = thenHave(in(t, x) ==> in(t, z)) by InstantiateForall(t)

    have(forall(t, in(t, y) ==> in(t, z))) by Tautology.from(subsetAxiom of (x := y, y := z, z := t))
    val second = thenHave(in(t, y) ==> in(t, z)) by InstantiateForall(t)

    have(in(t, setUnion(x, y)) ==> in(t, z)) by Tautology.from(first, second, setUnionMembership of (z := t))
    val defSubs = thenHave(forall(t, in(t, setUnion(x, y)) ==> in(t, z))) by RightForall
    have(thesis) by Tautology.from(defSubs, subsetAxiom of (x := setUnion(x, y), y := z))
  }

}
