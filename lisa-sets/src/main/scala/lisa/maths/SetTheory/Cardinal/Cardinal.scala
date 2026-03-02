package lisa.maths.SetTheory.Cardinal

import lisa.maths.SetTheory.Functions.Function.injective
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal._

object Cardinal extends lisa.Main:
  private val x, y, z, a = variable[Ind]
  private val A, B, X = variable[Ind]
  private val α, β, κ, δ, f, g = variable[Ind]
  private val C = variable[Class]

  /**
   * Definition --- The smallest limit ordinal
   */
  val ω = DEF(ε(α, limitOrdinal(α) /\ ∀(β, limitOrdinal(β) ==> (α <= β))))

  /**
   * Equinumerosity --- Two sets `A` and `B` are equinumerous (have the same cardinality)
   * if there exists a bijection (a one-to-one and onto function) from `A` to `B`.
   *
   * `equinumerosity(A, B) <=> ∃f, bijective(f)(A)(B)`
   *
   * @see [[bijective]]
   */
  val equinumerosity = DEF(λ(A, λ(B, ∃(f, bijective(f)(A)(B)))))

  /**
   * Dominates (Cardinality Less Than or Equal) --- Set `A` is dominated by set `B`
   * (or the cardinality of `A` is less than or equal to the cardinality of `B`, |A| <= |B|)
   * if there exists an injection (a one-to-one function) from `A` to `B`.
   *
   * `dominates(A, B) <=> ∃f, (f :: A -> B) /\ injective(f)(A)`
   *
   * The notation `(f :: A -> B)` means `f` is a function with domain `A` and codomain `B`.
   *
   * @see [[injective]]
   */
  val dominates = DEF(λ(A, λ(B, ∃(f, functionBetween(f)(A)(B) /\ injective(f)(A)))))

  /**
   * Local notations for cardinality
   */
  extension (α: Expr[Ind]) {
    inline infix def ≍(β: Expr[Ind]): Expr[Prop] = equinumerosity(α)(β)
    inline infix def ≲(β: Expr[Ind]): Expr[Prop] = dominates(α)(β)
    inline infix def ≨(β: Expr[Ind]): Expr[Prop] = dominates(α)(β) /\ ¬(equinumerosity(α)(β))
  }

  /**
   * Cardinal --- An ordinal `κ` is a cardinal if it is an initial ordinal,
   * meaning it is not equinumerous to any smaller ordinal.
   *
   * `cardinal(κ) <=> ordinal(κ) /\ ∀(α, α < κ ==> ¬(α ≍ κ))`
   */
  val cardinal = DEF(λ(κ, ordinal(κ) /\ ∀(α, (α < κ) ==> ¬(α ≍ κ))))

  /**
   * Cardinality Function --- The cardinality of a set A, denoted |A|,
   * is defined as the unique smallest ordinal in κ that is equinumerous to A.
   *
   * |A| <=> ε(κ, cardinal(κ) /\ A ≍ κ
   *
   * This function requires the Axiom of Choice (AC) to ensure the existence
   * of such a cardinal κ for every set A.
   */
  val card = DEF(λ(A, ε(κ, cardinal(κ) /\ (A ≍ κ))))

  /**
   * Regular Cardinal --- A cardinal κ is regular if for any function f from a
   * smaller ordinal α to κ, the range of f is bounded by some β < κ.
   *
   * regular(κ) <=> ∀α < κ, ∀f: α -> κ, ∃β < κ, range(f) ⊆ β
   */
  // val regular = DEF(
  //   λ(
  //     κ,
  //     ∀(
  //       α,
  //       ∀(
  //         f,
  //         (ordinal(α) /\ (α < κ) /\ (f :: α -> κ)) ==>
  //           ∃(β, (β < κ) /\ ∀(x, (x ∈ α) ==> (f(x) <= β)))
  //       )
  //     )
  //   )
  // )

  /**
   * Theorem ---
   */
  val cantorTheorem = Theorem(
    ∀(x, x ≨ 𝒫(x))
  ) {
    sorry
  }

  /**
   * Theorem ---
   */
  val cantorBernsteinTheorem = Theorem(
    (α ≲ β, β ≲ α) |- α ≍ β
  ) {
    assumeAll
    have(∃(f, functionBetween(f)(α)(β) /\ injective(f)(α)) /\ ∃(g, functionBetween(g)(β)(α) /\ injective(g)(β))) by Tautology.from(
      dominates.definition of (A := α, B := β),
      dominates.definition of (A := β, B := α, f := g)
    )
    sorry
  }

  // /**
  //  * Strong Limit Cardinal --- For any α < κ, |P(α)| < κ.
  //  * Using your notation: 𝒫(α) ≨ κ
  //  */
  // val strongLimit = DEF(λ(κ, ∀(α, (α < κ) ==> (𝒫(α) ≨ κ))))

  // /**
  //  * Strongly Inaccessible Cardinal
  //  * 1. Cardinal
  //  * 2. Uncountable (ω < κ)
  //  * 3. Regular
  //  * 4. Strong Limit
  //  */
  // val inaccessible = DEF(
  //   λ(
  //     κ,
  //     cardinal(κ) /\
  //       (ω < κ) /\
  //       regular(κ) /\
  //       strongLimit(κ)
  //   )
  // )
