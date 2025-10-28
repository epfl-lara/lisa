package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Order.Predef.*
import lisa.maths.SetTheory.Order.WellOrders.*

import lisa.maths.Quantifiers.∃!

import Ordinal.*
import WellOrder.*
import InitialSegment.*
import MembershipRelation.*

/**
 * Transfinite recursion is a process for creating a class-function by recursion
 * over the ordinals, as the limit of a sequence of set functions.
 */
object TransfiniteRecursion extends lisa.Main {

  private val α, β = variable[Ind]
  private val A, < = variable[Ind]
  private val F = variable[Ind >>: Ind >>: Ind]
  private val G = variable[Ind]

  extension (f: Expr[Ind]) {
    private inline def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * Transfinite recursion --- Given any `F : V -> V`, there exists a unique
   * `G : On -> V` such that for all ordinals `α`, `G(α) = F(G↾α)`.
   *
   * To state the theorem schema inside ZFC, we show that for any ordinal `α`,
   * there exists a unique function `g_α` defined by recursion over `α`.
   * We obtain the desired class-function `G` by setting `G(β) = g_α(β)` for any `α > β`.
   */
  val transfiniteRecursion = Theorem(
    ordinal(α) |- ∃(G, ∀(β ∈ α, G(β) === F(β)(G ↾ β)))
  ) {
    assume(ordinal(α))

    // Since `∈_α` is a well-order on `α`, we apply well-ordered recursion.
    val wellOrderedRecursion = have(∃(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))))))) by Tautology.from(
      ordinal.definition,
      WellOrderedRecursion.existence of (A := α, < := membershipRelation(α))
    )

    // It remains to replace `initialSegment(β, α, <)` with `β` under the binders.
    have(G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))) |- (G(β) === F(β)(G ↾ β))) by Congruence.from(Ordinal.ordinalInitialSegment)
    thenHave(β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α)))) |- β ∈ α ==> (G(β) === F(β)(G ↾ β))) by Tautology
    thenHave(∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))))) |- β ∈ α ==> (G(β) === F(β)(G ↾ β))) by LeftForall
    thenHave(∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))))) |- ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ β)))) by RightForall
    thenHave(∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))))) |- ∃(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ β))))) by RightExists
    thenHave(∃(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α)))))) |- ∃(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ β))))) by LeftExists

    have(thesis) by Cut(wellOrderedRecursion, lastStep)
  }

  /**
   * Definition --- Returns the function obtained by transfinite recursion of `F` until `α`.
   */
  val transfiniteRecursionFunction = DEF(λ(F, λ(α, ε(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ β)))))))
}
