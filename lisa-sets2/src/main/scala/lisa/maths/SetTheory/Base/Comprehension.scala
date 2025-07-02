package lisa.maths.SetTheory.Base

/**
  * This file defines the set-builder notation by using the (restricted) comprehension
  * schema.
  *
  * Example:
  * {{{
  * val z = {x ∈ y | φ(x)}
  * }}}
  */
object Comprehension extends lisa.Main {

  private val x, y, z = variable[Ind]

  /**
    * Restricted Set comprehension --- Given any set `y` and predicate `φ`,
    * creates the set `{x ∈ y | φ(x)}`.
    *
    * Its existence is guaranteed by the comprehension axiom schema.
    *
    * @param y set
    * @param φ predicate
    */
  private val setComprehension = DEF(λ(y, λ(φ, ε(z, ∀(x, x ∈ z <=> x ∈ y /\ φ(x)))))).printAs(args => {
    val y = args(0)
    val λ(x, φ) = (args(1).asInstanceOf[Expr[Ind >>: Prop]]: @unchecked) // φ is always of this form when using the notation
    s"{$x ∈ $y | $φ}"
  })

  extension (e: Expr[Prop]) {
    /** Notation for `{x ∈ y | φ}`.
      *
      * We explictly require `y` to be specified (no inference yet).
      *
      * @param φ Expression that may contain `x` as a free variable.
      */
    infix def | (φ: Expr[Prop]): Expr[Ind] =
      e match {
        case (x: Variable[Ind]) ∈ y =>
          /** {x ∈ y | φ(x)} */
          setComprehension(y)(λ(x, φ))

        case (x: Variable[Ind]) ⊆ y =>
          /** {x ⊆ y | φ(x)} */
          setComprehension(𝒫(y))(λ(x, φ))

        case x ∈ y =>
          throw new UnsupportedOperationException("Mixing replacement and comprehension is not yet supported.")

        case _ =>
          throw new IllegalArgumentException("Invalid set-builder notation.")
      }
  }

  /** Theorem --- For any `y` and `φ`, the set `z = {x ∈ y | φ(x)}` exists.
    *
    *   `∃ z. ∀ x. x ∈ z <=> x ∈ y /\ φ(x)`
    */
  val existence = Theorem(
    ∃(z, ∀(x, x ∈ z <=> x ∈ y /\ φ(x)))
  ) {
    have(thesis) by Restate.from(comprehensionSchema)
  }

  /** Theorem --- `x` is an element of `{x ∈ y | φ(x)}` if and only if `x ∈ y` and `φ(x)`.
    *
    *   `x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x)`
    */
  val membership = Theorem(
    x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x)
  ) {
    def P(z: Expr[Ind]) = ∀(x, x ∈ z <=> x ∈ y /\ φ(x))

    have(P(z) |- P(z)) by Hypothesis
    thenHave(P(z) |- P(ε(z, P(z)))) by RightEpsilon
    thenHave(P(z) |- ∀(x, x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x))) by Substitute(setComprehension.definition)
    thenHave(∃(z, P(z)) |- ∀(x, x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x))) by LeftExists
    thenHave(∃(z, P(z)) |- x ∈ {x ∈ y | φ(x)} <=> x ∈ y /\ φ(x)) by InstantiateForall(x)

    have(thesis) by Cut(existence, lastStep)
  }

  /**
    * Theorem --- The set `{x ∈ y | φ(x)}` is a subset of `y`.
    */
  val subset = Theorem(
    {x ∈ y | φ(x)} ⊆ y
  ) {
    have(x ∈ {x ∈ y | φ(x)} ==> x ∈ y) by Tautology.from(membership)
    thenHave(∀(x, x ∈ {x ∈ y | φ(x)} ==> x ∈ y)) by RightForall
    thenHave(thesis) by Substitute(⊆.definition)
  }

}
