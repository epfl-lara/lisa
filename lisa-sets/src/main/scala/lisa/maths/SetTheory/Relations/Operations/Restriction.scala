package lisa.maths.SetTheory.Relations.Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Definitions.*

/**
 * The restriction of a relation `R` to a domain `X` is the relation `R↾X`
 * consisting of pairs of elements `(x, y) ∈ R` such that `x ∈ X`.
 *
 * In other words, `R↾X = {(x, y) ∈ R | x ∈ X}`.
 *
 * TODO: Finish the proofs.
 */
object Restriction extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val X = variable[Ind]
  private val R, Q = variable[Ind]

  /**
   * Restriction --- For a relation `R`, its restriction to `X` is the set of
   * pairs of elements in `R` where the first element is in `X`. We denote it
   * by `R↾X`.
   *
   *   `R↾X = {(x, y) ∈ R | x ∈ X}`
   */
  val restriction = DEF(λ(R, λ(X, { z ∈ R | fst(z) ∈ X }))).printAs(args => {
    val R = args(0)
    val X = args(1)
    s"${R}↾${X}"
  })

  extension (R: set) {
    inline infix def ↾(X: set): set = restriction(R)(X)
  }

  /**
   * Theorem --- We have `(x, y) ∈ R ↾ X` <=> `(x, y) ∈ R` and `x ∈ X`.
   */
  val membership = Theorem(
    (x, y) ∈ (R ↾ X) <=> (x, y) ∈ R /\ (x ∈ X)
  ) {
    have((x, y) ∈ { z ∈ R | fst(z) ∈ X } <=> (x, y) ∈ R /\ (fst(x, y) ∈ X)) by Comprehension.apply
    thenHave(thesis) by Substitute(restriction.definition, Pair.pairFst)
  }

  /**
   * Theorem --- The relation `R` restricted to the empty domain is ∅.
   */
  val emptyRestriction = Theorem(
    (R ↾ ∅) === ∅
  ) {
    have(z ∈ { z ∈ R | fst(z) ∈ ∅ } <=> z ∈ R /\ (fst(z) ∈ ∅)) by Comprehension.apply
    thenHave(z ∈ (R ↾ ∅) <=> z ∈ R /\ (fst(z) ∈ ∅)) by Substitute(restriction.definition of (X := ∅))
    thenHave(z ∈ (R ↾ ∅) <=> z ∈ ∅) by Tautology.fromLastStep(
      EmptySet.definition of (x := fst(z)),
      EmptySet.definition of (x := z)
    )
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- The relation `R` restricted to its domain is `R`.
   */
  val restrictionToDomain = Theorem(
    (R ↾ dom(R)) === R
  ) {
    sorry
  }

  /**
   * Theorem --- Any subset `Q ⊆ R` of a relation `R` is itself a relation.
   */
  val subset = Theorem(
    (relation(R), Q ⊆ R) |- relation(Q)
  ) {
    sorry
  }

  /**
   * Restriction domain --- The domain of the restriction `R↾X` is `dom(R) ∩ X`.
   */
  val restrictionDomain = Theorem(
    dom(R ↾ X) === (dom(R) ∩ X)
  ) {
    sorry
  }

  /**
   * Restriction range --- The range of the restriction `R↾X` is a subset of `range(R)`.
   */
  val restrictionRange = Theorem(
    range(R ↾ X) ⊆ range(R)
  ) {
    sorry
  }

  /**
   * Extensionality --- If `x R y` whenever `x Q y` for all `x ∈ X`, then `R↾X = Q↾X`
   */
  val extensionality = Theorem(
    ∀(x, x ∈ X ==> ((x, y) ∈ (R ↾ X) <=> (x, y) ∈ (Q ↾ X))) |- (R ↾ X === Q ↾ X)
  ) {
    sorry
  }
}
