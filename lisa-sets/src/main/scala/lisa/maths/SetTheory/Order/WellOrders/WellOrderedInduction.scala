package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.*

import Definitions.*
import WellOrder.*

/**
 * Given a well-ordered set `(A, <)`, one can that a property `P` holds on `A`
 * by proving that `P(x)` holds for any `x ∈ A`, assuming that `P(y)` holds for
 * all `y < x`.
 */
object WellOrderedInduction extends lisa.Main {

  private val x, y = variable[Ind]
  private val A, B = variable[Ind]
  private val <, R = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /**
   * Well-ordered induction --- If `P(x)` holds for any `x ∈ A` assuming that
   * `P(y)` holds for all `y < x`, then `P(x)` holds for all `x ∈ A`.
   */
  val induction = Theorem(
    (
      wellOrdering(A)(<),
      ∀(x, x ∈ A ==> (∀(y, (y ∈ A) /\ ((y, x) ∈ <) ==> P(y)) ==> P(x)))
    ) |-
      ∀(x, x ∈ A ==> P(x))
  ) {
    assume(wellOrdering(A)(<))

    assume(∀(x, x ∈ A ==> (∀(y, (y ∈ A) /\ ((y, x) ∈ <) ==> P(y)) ==> P(x))))
    thenHave(x ∈ A ==> (∀(y, (y ∈ A) /\ ((y, x) ∈ <) ==> P(y)) ==> P(x))) by InstantiateForall(x)
    val inductionHypothesis = thenHave((x ∈ A, ∀(y, (y ∈ A) /\ ((y, x) ∈ <) ==> P(y))) |- P(x)) by Restate

    // Let S be the set of elements of `A` that do not satisfy `P`:
    val S = { x ∈ A | ¬(P(x)) }
    val `x ∈ S` = have(x ∈ S <=> (x ∈ A) /\ ¬(P(x))) by Comprehension.apply

    // By well-ordering, take `x` the `<`-least element ∈ `S`. We show that
    // `P(x)` holds, and thus there is a contradiction.
    have((x ∈ S, ∀(y, y ∈ S ==> (y, x) ∉ <)) |- P(x)) subproof {
      assume(x ∈ S)
      assume(∀(y, y ∈ S ==> (y, x) ∉ <))

      thenHave(y ∈ S ==> (y, x) ∉ <) by InstantiateForall(y)
      val `case y ∈ S` = thenHave(y ∈ S /\ ((y, x) ∈ <) ==> P(y)) by Tautology

      val `case y ∉ S` = have(y ∈ A /\ (y ∉ S) ==> P(y)) by Tautology.from(`x ∈ S` of (x := y))

      have(y ∈ A /\ ((y, x) ∈ <) ==> P(y)) by Tautology.from(`case y ∈ S`, `case y ∉ S`)
      thenHave(∀(y, y ∈ A /\ ((y, x) ∈ <) ==> P(y))) by RightForall
      thenHave(thesis) by Tautology.fromLastStep(inductionHypothesis, `x ∈ S`)
    }
    thenHave((x ∈ S, minimal(x)(S)(<)) |- P(x)) by Substitute(minimal.definition of (A := S, R := <))
    thenHave((x ∈ S) /\ minimal(x)(S)(<) |- ⊥) by Tautology.fromLastStep(`x ∈ S`)
    thenHave(∃(x, (x ∈ S) /\ minimal(x)(S)(<)) |- ⊥) by LeftExists
    thenHave(S === ∅) by Tautology.fromLastStep(
      WellOrder.minimalElement of (B := S),
      Comprehension.subset of (y := A, φ := λ(x, ¬(P(x))))
    )

    have(x ∉ S) by Congruence.from(EmptySet.definition, lastStep)
    thenHave(x ∈ A ==> P(x)) by Tautology.fromLastStep(`x ∈ S`)
    thenHave(thesis) by RightForall
  }
}
