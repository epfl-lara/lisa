package lisa.maths.SetTheory.Relations
package Operations

import lisa.maths.SetTheory.Base.Predef.{_, given}

import Relation._

/**
 * The converse of a relation `R` is the relation `R^T` such that `(x, y) ∈ R^T`
 * if and only if `(y, x) ∈ R`.
 */
object Converse extends lisa.Main {

  /**
   * Definition --- The converse of a relation `R` is the relation `R^T` such that
   * `(x, y) ∈ R^T` if `(y, x) ∈ R`.
   */
  val converse = DEF(λ(R, { (snd(z), fst(z)) | z ∈ R })).printAs(args => {
    val R = args(0)
    s"${R}^T"
  })

  /**
   * Theorem --- The converse operation is involutive, i.e., `(R^T)^T = R`.
   */
  val involution = Theorem(
    converse(converse(R)) === R
  ) {
    sorry
  }
}
