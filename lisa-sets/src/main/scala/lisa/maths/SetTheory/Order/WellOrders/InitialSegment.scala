package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef._

import PartialOrder._
import LowerSet._
import WellOrder._

/**
 * Given a well-order `(A, <)`, the set of all `y ∈ A` such that `y < x`
 * is called the initial segment of `A` induced by `x`, and is denoted `A_<x`.
 *
 * `initialSegment(x, A, <)` is a [[lowerSet]] of `A`. In fact, for a well-order
 * `(A, <)`, all lower sets are of the form `initialSegment(x, A, <)` for
 * some `x ∈ A`.
 */
object InitialSegment extends lisa.Main {

  private val S = variable[Ind]
  private val p = variable[Ind]

  /**
   * Definition --- The initial segment of `(A, <)` determined by `x` is the
   * set of elements `y ∈ A` that are less than `x`.
   */
  val initialSegment = DEF(λ(x, λ(A, λ(<, { y ∈ A | y < x })))).printAs(args => {
    val x = args(0)
    val A = args(1)
    val < = args(2)
    s"${A}_${<}${x}"
  })

  /**
   * Theorem --- `y ∈ A_<x` if and only if `y ∈ A` and `y < x`.
   *
   * Follows from [[Comprehension.membership]].
   */
  val membership = Theorem(
    y ∈ initialSegment(x)(A)(<) <=> (y ∈ A) /\ (y < x)
  ) {
    have(y ∈ { y ∈ A | y < x } <=> (y ∈ A) /\ (y < x)) by Comprehension.apply
    thenHave(thesis) by Substitute(initialSegment.definition)
  }

  /**
   * Lemma --- `A_<x ⊆ A`.
   */
  val subset = Theorem(
    initialSegment(x)(A)(<) ⊆ A
  ) {
    have(y ∈ initialSegment(x)(A)(<) ==> y ∈ A) by Tautology.from(membership)
    thenHave(∀(y ∈ initialSegment(x)(A)(<), y ∈ A)) by RightForall
    thenHave(thesis) by Substitute(⊆.definition)
  }

  /**
   * Theorem --- `A_<x` is a lower set of `(A, <)`.
   *
   * Follows by transitivity of `<`.
   */
  val isLowerSet = Theorem(
    (wellOrder(A)(<), x ∈ A) |- lowerSet(initialSegment(x)(A)(<))(A)(<)
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)

    have(y ∈ initialSegment(x)(A)(<) |- z ∈ A ==> ((z < y) ==> (z ∈ initialSegment(x)(A)(<)))) by Tautology.from(
      membership,
      membership of (y := z),
      WellOrder.transitivity,
      Relations.BasicTheorems.appliedTransitivity of (R := <, x := z, y := y, z := x, X := A)
    )
    thenHave(y ∈ initialSegment(x)(A)(<) |- ∀(z ∈ A, (z < y) ==> (z ∈ initialSegment(x)(A)(<)))) by RightForall
    thenHave(y ∈ initialSegment(x)(A)(<) ==> ∀(z ∈ A, (z < y) ==> (z ∈ initialSegment(x)(A)(<)))) by Restate
    thenHave(∀(y ∈ initialSegment(x)(A)(<), ∀(z ∈ A, (z < y) ==> (z ∈ initialSegment(x)(A)(<))))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      lowerSet.definition of (S := initialSegment(x)(A)(<)),
      subset
    )
  }

  /**
   * Theorem --- If `x < y` then `A_<x ∩ A_<y = A_<x`.
   */
  val intersection = Theorem(
    (wellOrder(A)(<), x < y, x ∈ A, y ∈ A) |-
      (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<)
  ) {
    assume(wellOrder(A)(<))
    assume(x < y)
    assume(x ∈ A)
    assume(y ∈ A)

    val I = (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<))

    have(z ∈ I <=> (z ∈ A) /\ ((z < x) /\ (z < y))) by Tautology.from(
      Intersection.membership of (x := initialSegment(x)(A)(<), y := initialSegment(y)(A)(<)),
      membership of (y := z, x := x),
      membership of (y := z, x := y)
    )
    thenHave(z ∈ I <=> (z ∈ A) /\ (z < x)) by Tautology.fromLastStep(
      WellOrder.transitivity,
      Relations.BasicTheorems.appliedTransitivity of (R := <, X := A, x := z, y := x, z := y)
    )
    thenHave(z ∈ I <=> (z ∈ initialSegment(x)(A)(<))) by Tautology.fromLastStep(
      membership of (y := z, x := x)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The intersection of two initial segments is an initial segment.
   *
   * Consequence of [[intersection]] and the trichotomy law on total orders.
   */
  val intersectionIsInitialSegment = Theorem(
    (wellOrder(A)(<), x ∈ A, y ∈ A) |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(y ∈ A)

    /**
     * There are 3 cases to consider:
     * - `x < y`
     * - `y < x`
     * - `x = y`
     */
    val `x < y` =
      have(x < y |- (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<)) by Tautology.from(intersection)
      thenHave(x < y |- x ∈ A /\ ((initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<))) by Tautology
      thenHave(x < y |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))) by RightExists

    // The case `y < x` is symmetrical to the case `x < y`.
    val `y < x` =
      have(y < x |- (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(y)(A)(<)) by Congruence.from(
        intersection of (x := y, y := x),
        Intersection.commutativity of (x := initialSegment(x)(A)(<), y := initialSegment(y)(A)(<))
      )
      thenHave(y < x |- y ∈ A /\ ((initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(y)(A)(<))) by Tautology
      thenHave(y < x |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))) by RightExists

    // For `x = y` the intersection is idempotent
    val `x = y` =
      have(x === y |- ((initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<))) by Congruence.from(Intersection.idempotence of (x := initialSegment(x)(A)(<)))
      thenHave(x === y |- x ∈ A /\ ((initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<))) by Tautology
      thenHave(x === y |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∩ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))) by RightExists

    have(thesis) by Tautology.from(
      WellOrder.totality,
      Relations.BasicTheorems.appliedTotality of (R := <, X := A),
      `x < y`,
      `y < x`,
      `x = y`
    )
  }

  /**
   * Theorem --- If `x < y` then `A_<x ∪ A_<y = A_<y`.
   */
  val union = Theorem(
    (wellOrder(A)(<), x < y, x ∈ A, y ∈ A) |-
      (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(y)(A)(<)
  ) {
    assume(wellOrder(A)(<))
    assume(x < y)
    assume(x ∈ A)
    assume(y ∈ A)

    val U = (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<))

    have(z ∈ U <=> (z ∈ A) /\ ((z < x) \/ (z < y))) by Tautology.from(
      Union.membership of (x := initialSegment(x)(A)(<), y := initialSegment(y)(A)(<)),
      membership of (y := z, x := x),
      membership of (y := z, x := y)
    )
    thenHave(z ∈ U <=> (z ∈ A) /\ (z < y)) by Tautology.fromLastStep(
      WellOrder.transitivity,
      Relations.BasicTheorems.appliedTransitivity of (R := <, X := A, x := z, y := x, z := y)
    )
    thenHave(z ∈ U <=> (z ∈ initialSegment(y)(A)(<))) by Tautology.fromLastStep(
      membership of (y := z, x := y)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The union of two initial segments is an initial segment.
   *
   * Consequence of [[union]] and the trichotomy law on total orders.
   */
  val unionIsInitialSegment = Theorem(
    (wellOrder(A)(<), x ∈ A, y ∈ A) |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(y ∈ A)

    /**
     * There are 3 cases to consider:
     * - `x < y`
     * - `y < x`
     * - `x = y`
     */
    val `x < y` =
      have(x < y |- (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(y)(A)(<)) by Tautology.from(union)
      thenHave(x < y |- y ∈ A /\ ((initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(y)(A)(<))) by Tautology
      thenHave(x < y |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))) by RightExists

    // The case `y < x` is symmetrical to the case `x < y`.
    val `y < x` =
      have(y < x |- (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<)) by Congruence.from(
        union of (x := y, y := x),
        Union.commutativity of (x := initialSegment(x)(A)(<), y := initialSegment(y)(A)(<))
      )
      thenHave(y < x |- x ∈ A /\ ((initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<))) by Tautology
      thenHave(y < x |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))) by RightExists

    // For `x = y` the union is idempotent
    val `x = y` =
      have(x === y |- ((initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<))) by Congruence.from(Union.idempotence of (x := initialSegment(x)(A)(<)))
      thenHave(x === y |- x ∈ A /\ ((initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(x)(A)(<))) by Tautology
      thenHave(x === y |- ∃(z ∈ A, (initialSegment(x)(A)(<) ∪ initialSegment(y)(A)(<)) === initialSegment(z)(A)(<))) by RightExists

    have(thesis) by Tautology.from(
      WellOrder.totality,
      Relations.BasicTheorems.appliedTotality of (R := <, X := A),
      `x < y`,
      `y < x`,
      `x = y`
    )
  }

  /**
   * Theorem --- If `x < y` then `A_<x ⊆ A_<y`.
   */
  val monotonic = Theorem(
    (wellOrder(A)(<), x ∈ A, y ∈ A, x < y) |- initialSegment(x)(A)(<) ⊆ initialSegment(y)(A)(<)
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(y ∈ A)
    assume(x < y)

    have(z ∈ initialSegment(x)(A)(<) ==> z ∈ initialSegment(y)(A)(<)) by Tautology.from(
      membership of (y := z),
      membership of (y := z, x := y),
      WellOrder.transitivity,
      Relations.BasicTheorems.appliedTransitivity of (R := <, X := A, x := z, y := x, z := y)
    )
    thenHave(∀(z, z ∈ initialSegment(x)(A)(<) ==> z ∈ initialSegment(y)(A)(<))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := initialSegment(x)(A)(<), y := initialSegment(y)(A)(<)))
  }

  /**
   * Theorem --- `(A_<x)_<x = A_<x`
   */
  val idempotence = Theorem(
    initialSegment(x)(initialSegment(x)(A)(<))(<) === initialSegment(x)(A)(<)
  ) {
    have(y ∈ initialSegment(x)(initialSegment(x)(A)(<))(<) <=> y ∈ initialSegment(x)(A)(<)) by Tautology.from(membership, membership of (A := initialSegment(x)(A)(<)))
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- For any `y < x` we have `(A_<x)_<y = A_<y`.
   */
  val absorption = Theorem(
    (wellOrder(A)(<), x ∈ A, y ∈ initialSegment(x)(A)(<)) |- initialSegment(y)(initialSegment(x)(A)(<))(<) === initialSegment(y)(A)(<)
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(y ∈ initialSegment(x)(A)(<))

    have(z ∈ initialSegment(y)(initialSegment(x)(A)(<))(<) <=> z ∈ initialSegment(y)(A)(<)) by Tautology.from(
      membership of (y := z, x := y, A := initialSegment(x)(A)(<)),
      membership of (y := z, x := y),
      membership of (y := z),
      membership,
      WellOrder.transitivity,
      Relations.BasicTheorems.appliedTransitivity of (R := <, X := A, x := z, y := y, z := x)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- If `x = p + 1` (`p` is the predecessor of `x`) then `A_<x = A_<p ∪ {p}`.
   */
  val successor = Theorem(
    (wellOrder(A)(<), x ∈ A, p ∈ A, p < x, ¬(∃(y ∈ A, (p < y) /\ (y < x)))) |- initialSegment(x)(A)(<) === (initialSegment(p)(A)(<) ∪ singleton(p))
  ) {
    assume(wellOrder(A)(<))
    assume(x ∈ A)
    assume(p ∈ A)
    assume(p < x)
    assume(¬(∃(y ∈ A, (p < y) /\ (y < x))))
    thenHave(∀(y ∈ A, (y < x) ==> ¬(p < y))) by Restate
    thenHave(y ∈ A |- (y < x) ==> ¬(p < y)) by InstantiateForall(y)
    val `==>` = thenHave((y ∈ A, y < x) |- (y < p) \/ (y === p)) by Tautology.fromLastStep(
      WellOrder.totality,
      Relations.BasicTheorems.appliedTotality of (R := <, X := A, x := p, y := y)
    )

    // We show the converse direction of `y < x <=> (y < p) \/ (y = p)`
    val `y < p` = have((y ∈ A, y < p) |- y < x) by Tautology.from(
      WellOrder.transitivity,
      Relations.BasicTheorems.appliedTransitivity of (R := <, X := A, x := y, y := p, z := x)
    )
    val `y = p` = have((y ∈ A, y === p) |- y < x) by Congruence
    val `<==` = have((y ∈ A, (y < p) \/ (y === p)) |- y < x) by LeftOr(`y < p`, `y = p`)

    val s = (have(y === p |- y ∈ A) by Congruence)

    have(y ∈ initialSegment(x)(A)(<) <=> (y ∈ A) /\ (y < x)) by Tautology.from(membership)
    thenHave(y ∈ initialSegment(x)(A)(<) <=> (y ∈ A) /\ ((y < p) \/ (y === p))) by Tautology.fromLastStep(`==>`, `<==`)
    thenHave(y ∈ initialSegment(x)(A)(<) <=> (y ∈ initialSegment(p)(A)(<)) \/ (y ∈ singleton(p))) by Tautology.fromLastStep(
      membership of (x := p),
      Singleton.membership of (x := p),
      s
    )
    thenHave(y ∈ initialSegment(x)(A)(<) <=> y ∈ (initialSegment(p)(A)(<) ∪ singleton(p))) by Substitute(
      Union.membership of (z := y, x := initialSegment(p)(A)(<), y := singleton(p))
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- For any `B ⊆ A` we have `initialSegment(x, B, <) = initialSegment(x, A, <) ∩ B`.
   */
  val ofSubset = Theorem(
    (wellOrder(A)(<), B ⊆ A, x ∈ A) |- initialSegment(x)(B)(<) === (initialSegment(x)(A)(<) ∩ B)
  ) {
    assume(wellOrder(A)(<))
    assume(B ⊆ A)
    assume(x ∈ A)

    have(y ∈ initialSegment(x)(B)(<) <=> (y ∈ (initialSegment(x)(A)(<) ∩ B))) by Tautology.from(
      membership,
      membership of (A := B),
      Intersection.membership of (z := y, x := initialSegment(x)(A)(<), y := B),
      Subset.membership of (x := B, y := A, z := y)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- If `(A, <)` is a well-order, then `(initialSegment(x, A, <), <)`
   * is also a well-order.
   */
  val ofWellOrder = Theorem(
    wellOrder(A)(<) |- wellOrder(initialSegment(x)(A)(<))(<)
  ) {
    assume(wellOrder(A)(<))

    // Since `initialSegment(x, A, <) ⊆ A` the total order is inherited from `A`

    sorry
  }
}
