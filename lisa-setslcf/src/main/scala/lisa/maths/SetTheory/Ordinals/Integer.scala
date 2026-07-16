package lisa.maths.SetTheory.Ordinals

import Ordinal._

/**
 * This file defines integers as ordinals whose elements are either zero
 * or successor ordinals.
 *
 * `ω` is defined as the set of all integers, and is itself an ordinal which
 * is limit.
 */
object Integer extends lisa.Main {

  private val x = variable[Ind]
  private val α, β = variable[Ind]

  /**
   * Definition --- An ordinal `α` is an integer if and only if all its predecessors are zero or successors.
   */
  val integer = DEF(λ(α, ∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))))

  /**
   * Definition --- The set of all integers is the set denoted `ω`.
   *
   * Its existence is guaranteed by the [[infinityAxiom]].
   */
  val ω = DEF(ε(x, ∀(α, α ∈ x <=> integer(α))))

}
