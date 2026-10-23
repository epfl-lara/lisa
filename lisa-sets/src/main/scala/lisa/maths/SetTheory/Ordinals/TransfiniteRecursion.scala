package lisa.maths.SetTheory.Ordinals

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Order.WellOrders._
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation

import Ordinal._
import InitialSegment._
import MembershipRelation._

/**
 * Transfinite recursion is a process for creating a class-function by recursion
 * over the ordinals, as the limit of a sequence of set functions.
 */
object TransfiniteRecursion extends lisa.Main {

  private val α, β = variable[Ind]
  private val A, < = variable[Ind]
  private val x = variable[Ind]
  private val F = variable[Ind >>: Ind >>: Ind]
  private val Func = variable[Ind >>: Ind >>: Ind]
  private val G = variable[Ind]
  private val P = variable[Ind >>: Prop]

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
    have((G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))), β ∈ α) |- (G(β) === F(β)(G ↾ β))) by Congruence.from(Ordinal.ordinalInitialSegment)
    thenHave(β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α)))) |- β ∈ α ==> (G(β) === F(β)(G ↾ β))) by Tautology
    thenHave(∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))))) |- β ∈ α ==> (G(β) === F(β)(G ↾ β))) by LeftForall
    thenHave(∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))))) |- ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ β)))) by RightForall
    thenHave(∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α))))) |- ∃(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ β))))) by RightExists
    thenHave(∃(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ initialSegment(β)(α)(membershipRelation(α)))))) |- ∃(G, ∀(β, β ∈ α ==> (G(β) === F(β)(G ↾ β))))) by LeftExists

    have(thesis) by Cut(wellOrderedRecursion, lastStep)
  }

  /**
   * Strengthened existence theorem — the recursive graph is chosen as a
   * function on `α`.
   */
  val transfiniteRecursionWithFunctionOn =
    Theorem(ordinal(α) |- ∃(G, functionOn(G)(α) /\ ∀(β ∈ α, G(β) === Func(β)(G ↾ β)))) {
      assume(ordinal(α))

      val rec = WellOrderedRecursion.recursiveFunctionOn(Func)(α)(membershipRelation(α))

      val recSpec = have(
        functionOn(rec)(α) /\
          ∀(β ∈ α, rec(β) === Func(β)(rec ↾ initialSegment(β)(α)(membershipRelation(α))))
      ) by Tautology.from(
        ordinal.definition,
        WellOrderedRecursion.recursiveFunctionOnSpec
          .of(A := α, < := membershipRelation(α), Func := Func)
      )

      val recEqOnInit = have(
        ∀(β ∈ α, rec(β) === Func(β)(rec ↾ initialSegment(β)(α)(membershipRelation(α))))
      ) by Tautology.from(recSpec)

      val recEq = have(∀(β ∈ α, rec(β) === Func(β)(rec ↾ β))) subproof {
        val recAtBeta = have(
          β ∈ α |- rec(β) === Func(β)(rec ↾ initialSegment(β)(α)(membershipRelation(α)))
        ) by InstantiateForall(β)(recEqOnInit)
        val segEq = have(β ∈ α |- initialSegment(β)(α)(membershipRelation(α)) === β) by
          Tautology.from(Ordinal.ordinalInitialSegment)
        have(β ∈ α |- rec(β) === Func(β)(rec ↾ β)) by Congruence.from(recAtBeta, segEq)
        thenHave(β ∈ α ==> (rec(β) === Func(β)(rec ↾ β))) by Restate
        thenHave(thesis) by RightForall
      }

      val recFunOn = have(functionOn(rec)(α)) by Tautology.from(recSpec)
      have(functionOn(rec)(α) /\ ∀(β ∈ α, rec(β) === Func(β)(rec ↾ β))) by
        Tautology.from(recFunOn, recEq)
      thenHave(thesis) by RightExists
    }

  /**
   * Definition --- Returns the function obtained by transfinite recursion of
   * `Func` until `α`, additionally required to be a function on `α`.
   */
  val transfiniteRecursionFunction = DEF(
    λ(Func, λ(α, ε(G, functionOn(G)(α) /\ ∀(β, β ∈ α ==> (G(β) === Func(β)(G ↾ β))))))
  )

  /**
   * Spec theorem for [[transfiniteRecursionFunction]].
   */
  val transfiniteRecursionFunctionSpec = Theorem(
    ordinal(α) |-
      (functionOn(transfiniteRecursionFunction(Func)(α))(α) /\ ∀(
        β ∈ α,
        transfiniteRecursionFunction(Func)(α)(β) ===
          Func(β)(transfiniteRecursionFunction(Func)(α) ↾ β)
      ))
  ) {
    assume(ordinal(α))

    val body = functionOn(G)(α) /\ ∀(β, β ∈ α ==> (G(β) === Func(β)(G ↾ β)))
    val eps = ε(G, body)
    val rec = transfiniteRecursionFunction(Func)(α)

    val ex0 = have(∃(G, body)) by Restate.from(transfiniteRecursionWithFunctionOn)
    val epsProp = have(body.substitute(G := eps)) by
      Cut(ex0, Quantifiers.existsEpsilon.of(x := G, P := λ(G, body)))

    val epsFunOn = have(functionOn(eps)(α)) by Tautology.from(epsProp)
    val epsEq = have(∀(β ∈ α, eps(β) === Func(β)(eps ↾ β))) by Tautology.from(epsProp)

    val defEq = transfiniteRecursionFunction.definition.of(Func := Func, α := α)

    val recFunOn = have(functionOn(rec)(α)) by Congruence.from(epsFunOn, defEq)

    val recEq = {
      have(β ∈ α |- rec(β) === Func(β)(rec ↾ β)) subproof {
        assume(β ∈ α)
        val eqAtBeta = have(eps(β) === Func(β)(eps ↾ β)) by InstantiateForall(β)(epsEq)
        have(thesis) by Congruence.from(eqAtBeta, defEq)
      }
      thenHave(β ∈ α ==> (rec(β) === Func(β)(rec ↾ β))) by Restate
      thenHave(∀(β ∈ α, rec(β) === Func(β)(rec ↾ β))) by RightForall
    }

    have(thesis) by Tautology.from(recFunOn, recEq)
  }
}
