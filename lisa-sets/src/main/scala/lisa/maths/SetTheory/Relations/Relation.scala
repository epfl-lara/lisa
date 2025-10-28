package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef.{*, given}

/**
 * A relation between `X` and `Y` is a subset `R` of the [[CartesianProduct]]
 * `X × Y`, where `(x, y) ∈ R` means that `x` is related to `y`.
 *
 * This file defines:
 * - (Binary) relations, homogeneous relations
 * - Relation domain, range and field
 */
object Relation extends lisa.Main {

  /** Relation symbol. */
  val R = variable[Ind]

  /**
   * Definition --- A set `R` is a relation between `X` and `Y` if `R` is
   * a subset of the Cartesian product `X × Y`.
   *
   *   `relationBetween(R, X, Y) <=> R ⊆ X × Y`
   */
  val relationBetween = DEF(λ(R, λ(X, λ(Y, R ⊆ (X × Y)))))

  /**
   * Definition --- A set `R` is a relation on `X` if `R` only contains pairs
   * of elements of `X`.
   *
   *   `relationOn(R, X) <=> R ⊆ X × X`
   */
  val relationOn = DEF(λ(R, λ(X, R ⊆ (X × X))))

  /**
   * Definition --- A set `R` is a relation if there exists sets `X` and `Y`
   * such that `R` is a relation between `X` and `Y`.
   *
   *   `relation(R) <=> ∃ X, Y. R ⊆ X × Y`
   */
  val relation = DEF(λ(R, ∃(X, ∃(Y, R ⊆ (X × Y)))))

  extension (x: Expr[Ind]) {
    /** We write `x R y` instead of `(x, y) ∈ R`. */
    private[Relations] infix def R(y: Expr[Ind]): Expr[Prop] = (x, y) ∈ Relation.R
  }

  /**
   * Definition --- The domain of a relation `R` is the set of elements that
   * are related to another element.
   *
   *   `dom(R) = {x | (x, y) ∈ R }`
   */
  val dom = DEF(λ(R, { fst(z) | z ∈ R }))

  /**
   * Definition --- The range of a relation `R` is the set of elements that
   * have an element related to them.
   *
   *   `range(R) = {y | (x, y) ∈ R}`
   */
  val range = DEF(λ(R, { snd(z) | z ∈ R }))

  /**
   * Definition --- The field of a relation `R` is the union of its domain and
   * its range.
   *
   *   `field(R) = dom(R) ∪ range(R)`
   */
  val field = DEF(λ(R, dom(R) ∪ range(R)))

}
