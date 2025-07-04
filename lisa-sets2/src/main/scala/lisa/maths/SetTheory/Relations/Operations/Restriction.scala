package lisa.maths.SetTheory.Relations.Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Definitions.*

/** The restriction of a relation `ℛ` to a domain `X` is the relation `ℛ↾X`
  * consisting of pairs of elements `(x, y) ∈ ℛ` such that `x ∈ X`.
  *
  * In other words, `ℛ↾X = {(x, y) ∈ ℛ | x ∈ X}`.
  *
  * TODO: Finish the proofs.
  */
object Restriction extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val X = variable[Ind]
  private val ℛ, 𝒬 = variable[Ind]

  /** Restriction --- For a relation `ℛ`, its restriction to `X` is the set of
    * pairs of elements in `ℛ` where the first element is in `X`. We denote it
    * by `ℛ↾X`.
    *
    *   `ℛ↾X = {(x, y) ∈ ℛ | x ∈ X}`
    */
  val restriction = DEF(λ(ℛ, λ(X, { z ∈ ℛ | fst(z) ∈ X }))).printAs(args => {
    val ℛ = args(0)
    val X = args(1)
    s"${ℛ}↾${X}"
  })

  extension (ℛ : set) {
    inline infix def ↾(X: set): set = restriction(ℛ)(X)
  }

  /**
    * Theorem --- We have `(x, y) ∈ ℛ ↾ X` <=> `(x, y) ∈ ℛ` and `x ∈ X`.
    */
  val membership = Theorem(
    (x, y) ∈ (ℛ ↾ X) <=> (x, y) ∈ ℛ /\ (x ∈ X)
  ) {
    have((x, y) ∈ { z ∈ ℛ | fst(z) ∈ X } <=> (x, y) ∈ ℛ /\ (fst(x, y) ∈ X)) by Comprehension.apply
    thenHave(thesis) by Substitute(restriction.definition, Pair.pairFst)
  }

  /** Theorem --- The relation `ℛ` restricted to the empty domain is ∅.
    */
  val emptyRestriction = Theorem(
    (ℛ ↾ ∅) === ∅
  ) {
    have(z ∈ { z ∈ ℛ | fst(z) ∈ ∅ } <=> z ∈ ℛ /\ (fst(z) ∈ ∅)) by Comprehension.apply
    thenHave(z ∈ (ℛ ↾ ∅) <=> z ∈ ℛ /\ (fst(z) ∈ ∅)) by Substitute(restriction.definition of (X := ∅))
    thenHave(z ∈ (ℛ ↾ ∅) <=> z ∈ ∅) by Tautology.fromLastStep(
      EmptySet.definition of (x := fst(z)),
      EmptySet.definition of (x := z),
    )
    thenHave(thesis) by Extensionality
  }

  /** Theorem --- The relation `ℛ` restricted to its domain is `ℛ`.
    */
  val restrictionToDomain = Theorem(
    (ℛ ↾ dom(ℛ)) === ℛ
  ) {
    sorry
  }

  /**
    * Theorem --- Any subset `𝒬 ⊆ ℛ` of a relation `ℛ` is itself a relation.
    */
  val subset = Theorem(
    (relation(ℛ), 𝒬 ⊆ ℛ) |- relation(𝒬)
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

