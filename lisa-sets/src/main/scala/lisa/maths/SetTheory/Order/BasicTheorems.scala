package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Predef._

import PartialOrder._
import Extrema._

/**
 * Properties and theorems about orders.
 */
object BasicTheorems extends lisa.Main {

  private val Q = variable[Ind]

  /**
   * Theorem --- A `R`-minimal element `a` is also `Q`-minimal for any `Q ⊆ R`.
   */
  val minimalElementSubset = Theorem(
    (minimal(a)(A)(R), Q ⊆ R) |- minimal(a)(A)(Q)
  ) {
    assume(minimal(a)(A)(R))
    assume(Q ⊆ R)

    val `a ∈ A` = have(a ∈ A) by Tautology.from(minimal.definition of (< := R))

    have(∀(x, x ∈ A ==> ¬((x, a) ∈ R))) by Tautology.from(minimal.definition of (< := R))
    thenHave(x ∈ A ==> ¬((x, a) ∈ R)) by InstantiateForall(x)
    thenHave(x ∈ A ==> ¬((x, a) ∈ Q)) by Tautology.fromLastStep(
      Subset.membership of (x := Q, y := R, z := (x, a))
    )
    thenHave(∀(x, x ∈ A ==> ¬((x, a) ∈ Q))) by Generalize

    have(a ∈ A /\ ∀(x, x ∈ A ==> ¬((x, a) ∈ Q))) by RightAnd(`a ∈ A`, lastStep)
    thenHave(thesis) by Substitute(minimal.definition of (< := Q))
  }
}
