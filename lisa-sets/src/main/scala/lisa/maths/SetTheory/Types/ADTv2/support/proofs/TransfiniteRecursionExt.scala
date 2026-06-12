package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Order.WellOrders.InitialSegment.initialSegment
import lisa.maths.SetTheory.Order.WellOrders.WellOrderedRecursion
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinal
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinalInitialSegment
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation.membershipRelation
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._

/**
 * Extension of TransfiniteRecursion with a strengthened DEF (the ε-selector
 * additionally requires functionOn) and the accompanying spec theorem.
 *
 * These results are kept here rather than in the library so that the library
 * file TransfiniteRecursion.scala is not modified.
 */
object TransfiniteRecursionExt {

  private val < = variable[Ind]
  private val Func = variable[Ind >>: Ind >>: Ind]
  private val G = variable[Ind]

  extension (f: Expr[Ind]) {
    private inline def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
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
          Tautology.from(ordinalInitialSegment)
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
   * Definition — Returns the function obtained by transfinite recursion of
   * `Func` until `α`, additionally required to be a function on `α`.
   */
  val transfiniteRecursionFunction = DEF(
    λ(Func, λ(α, ε(G, functionOn(G)(α) /\ ∀(β, β ∈ α ==> (G(β) === Func(β)(G ↾ β))))))
  )

  /** Spec theorem for [[transfiniteRecursionFunction]]. */
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
