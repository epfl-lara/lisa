package lisa.maths.settheory

import lisa.automation.Substitution.{Apply as Substitute}

/**
 * Set-theoretic comprehension and set builder notations.
 *
 * Example:
 * {{{
 * val z = {x ∈ y | φ(x)}
 * }}}
 */
object Comprehension extends lisa.Main {

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]
  val t = variable[Ind]
  val s = variable[Ind]

  chapter("Set comprehension")

  section("Full set comprehension")

  /**
   * Unrestricted Set comprehension --- Given any predicate `φ`, creates the set `{x | φ(x)}`.
   *
   * Its assumption as an axiom schema leads to contradictions, as indicated by Russell's paradox.
   *
   * @param φ predicate
   * @see [[SetTheory.russellsParadox]]
   */
  val fullComprehension = DEF(λ(φ, ε(y, ∀(x, x ∈ y <=> φ(x)))))

  /**
   * Theorem --- Russel's Paradox: `{x | x ∉ x}` is not a set.
   *
   *   `∃y. ∀x. x ∈ y <=> x ∉ x |- ⊥`
   */
  val russellsParadox = Theorem(
    ∃(y, ∀(x, x ∈ y <=> x ∉ x)) |- ()
  ) {
    have(y ∈ y <=> y ∉ y |- ()) by Tautology
    thenHave(∀(x, x ∈ y <=> x ∉ x) |- ()) by LeftForall
    thenHave(∃(y, ∀(x, x ∈ y <=> x ∉ x)) |- ()) by LeftExists
  }

  section("Restricted set comprehension")

  /**
   * Restricted Set comprehension --- Given any set `y` and predicate `φ`, creates the set `{x ∈ y | φ(x)}`.
   *
   * Its existence is guaranteed by the comprehension axiom schema.
   *
   * @param y set
   * @param φ predicate
   */
  val setComprehension = DEF(λ(y, λ(φ, ε(z, ∀(x, x ∈ z <=> x ∈ y /\ φ(x)))))).printAs(args => {
    val y = args(0)
    val φ = args(1).asInstanceOf[Expr[Ind >>: Prop]]
    val λ(x, φ_) = (φ: @unchecked)
    s"{$x ∈ $y | ${φ_}}"
  })

  extension (e: Expr[Prop]) {
    /** Notation for `{x ∈ y | φ}`. */
    infix def | (φ: Expr[Prop]): Expr[Ind] =
      e match {
        case In(x: Variable[?], y) =>
          setComprehension(y)(λ(x, φ))
        case In(e, y) =>
          throw new UnsupportedOperationException("Replacement schema syntax is not yet supported.")
        case _ =>
          throw new IllegalArgumentException("Invalid comprehension.")
      }
  }

  /** Theorem --- For any `y` and `φ`, the set `z = {x ∈ y | φ(x)}` exists.
   *
   *   `∃ z. ∀ x. x ∈ z <=> x ∈ y /\ φ(x)`
   */
  val comprehensionExistence = Theorem(
    ∃(z, ∀(x, x ∈ z <=> x ∈ y /\ φ(x)))
  ) {
    have(thesis) by Restate.from(comprehensionSchema)
  }

  /** Theorem --- `x` is an element of `{x ∈ y | φ(x)}` if and only if `x ∈ y` and `φ(x)`.
   *
   *   `∃ z. ∀ x. x ∈ z <=> x ∈ y /\ φ(x)
   */
  val comprehensionMembership = Theorem(
    ∀(x, x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x))
  ) {
    def P(z: Expr[Ind]) = ∀(x, x ∈ z <=> x ∈ y /\ φ(x))

    have(P(z) |- P(z)) by Restate
    thenHave(P(z) |- P(ε(z, P(z)))) by RightEpsilon
    thenHave(P(z) |- ∀(x, x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x))) by Substitute(setComprehension.definition)
    thenHave(∃(z, P(z)) |- ∀(x, x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x))) by LeftExists

    have(thesis) by Cut(comprehensionExistence, lastStep)
  }

}
