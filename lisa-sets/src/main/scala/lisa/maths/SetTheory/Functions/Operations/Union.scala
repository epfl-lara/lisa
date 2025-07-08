package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}

import Definitions.*

/**
 * If `f` and `g` are two functions that agree on the intersection of their
 * domains, then `f ∪ g` is a function on the union of their domains.
 *
 * Note that in general, the union of two functions is not a function, as they
 * may disagree on the intersection of their domains.
 */
object Union extends lisa.Main {

  private val f, g = variable[Ind]
  private val S = variable[Ind]

  /**
   * Theorem --- The ∪ of a set of functions that are subsets of each other
   * is a function.
   */
  val isFunction = Theorem(
    (
      ∀(f, f ∈ S ==> function(f)),
      ∀(f, ∀(g, (f ∈ S) /\ (g ∈ S) ==> (f ⊆ g) \/ (g ⊆ f)))
    ) |- function(⋃(S))
  ) {
    sorry
  }

}
