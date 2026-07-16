package lisa.maths.SetTheory.Relations
package Operations

import lisa.maths.SetTheory.Base.Predef._

/**
 * The converse of a relation `R` is the relation `¬R` such that `(x, y) ∈ ¬R`
 * if and only if `(x, y) ∉ R`.
 */
object Complement extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val R = variable[Ind]
  private val X = variable[Ind]

  /**
   * Definition --- The complement of `R` on `X` is the set of pairs `(x, y) ∈ (X × X)`
   * such that `(x, y) ∉ R`.
   */
  val complement = DEF(λ(R, λ(X, { z ∈ (X × X) | z ∉ R })))

}
