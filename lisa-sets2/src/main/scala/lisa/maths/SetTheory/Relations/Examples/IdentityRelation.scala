package lisa.maths.SetTheory.Relations
package Examples

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Predef.*

/** The identity or diagonal relation `Δ(X)` on `X` is the set of pairs `(x, x)`
  * for `x ∈ X`. It is the smallest [[equivalence]] relation on `X`.
  */
object IdentityRelation extends lisa.Main {

  private val X = variable[Ind]
  private val x, y = variable[Ind]
  private val ℛ = variable[Ind]

  /** Identity relation --- The identity relation on `X`, also called the
    * diagonal of `X`, is the set `Δ(X)` of pairs `(x, x)` for `x ∈ X`.
    */
  val Δ = DEF(λ(X, { (x, x) | x ∈ X }))

  /** Theorem --- A relation `ℛ` is reflexive on `X` <=> `Δ(X) ⊆ ℛ`.
    */
  val identityRelationSubset = Theorem(
    reflexive(ℛ)(X) <=> Δ(X) ⊆ ℛ
  ) {
    sorry
  }
}
