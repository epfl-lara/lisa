package lisa.maths.SetTheory.Relations.Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Definitions.*

/** The restriction of a relation `ℛ` to a domain `X` is the relation `ℛ↾X`
  * consisting of pairs of elements `(x, y) ∈ ℛ` such that `x ∈ X`.
  *
  * In other words, `ℛ↾X = ℛ ∩ (X × range(ℛ))`.
  *
  * TODO: Finish the proofs.
  */
object Restriction extends lisa.Main {

  private val x, y = variable[Ind]
  private val X = variable[Ind]
  private val ℛ, 𝒬 = variable[Ind]

  /** Restriction --- For a relation `ℛ`, its restriction to `X` is the set of
    * pairs of elements in `ℛ` where the first element is in `X`. We denote it
    * by `ℛ↾X`.
    *
    *   `ℛ↾X = ℛ ∩ (X × range(ℛ))`
    */
  val restriction = DEF(λ(ℛ, λ(X, ℛ ∩ (X × range(ℛ))))).printAs(args => {
    val ℛ = args(0)
    val X = args(1)
    s"${ℛ}↾${X}"
  })

  extension (ℛ : set) {
    inline infix def ↾(X: set): set = restriction(ℛ)(X)
  }

  /** Theorem --- The relation `ℛ` restricted to the empty domain is ∅.
    */
  val emptyRestriction = Theorem(
    (ℛ ↾ ∅) === ∅
  ) {
    sorry
  }

  /** Restriction domain --- The domain of the restriction `ℛ↾X` is `dom(ℛ) ∩ X`.
    */
  val restrictionDomain = Theorem(
    dom(ℛ↾X) === (dom(ℛ) ∩ X)
  ) {
    sorry
  }

  /** Restriction range --- The range of the restriction `ℛ↾X` is a subset of `range(ℛ)`.
    */
  val restrictionRange = Theorem(
    range(ℛ↾X) ⊆ range(ℛ)
  ) {
    sorry
  }

  /** Extensionality --- If `x ℛ y` whenever `x 𝒬 y` for all `x ∈ X`, then `ℛ↾X = 𝒬↾X`
    */
  val extensionality = Theorem(
    ∀(x, x ∈ X ==> ((x, y) ∈ (ℛ↾X) <=> (x, y) ∈ (𝒬↾X))) |- (ℛ↾X === 𝒬↾X)
  ) {
    sorry
  }
}

