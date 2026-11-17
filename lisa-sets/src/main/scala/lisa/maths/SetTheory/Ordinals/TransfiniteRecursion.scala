package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Order.WellOrders._
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation

import Ordinal._
import InitialSegment._
import MembershipRelation._

/**
 * Constructs functions by recursion over an ordinal.
 */
object TransfiniteRecursion extends lisa.Main {

  private val α, β = variable[Ind]
  private val A, < = variable[Ind]
  private val F, Func = variable[Ind >>: Ind >>: Ind]
  private val G = variable[Ind]

  extension (f: Expr[Ind]) {
    private inline def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * The function obtained by well-ordered recursion on ordinal membership.
   */
  val transfiniteRecursionFunction = DEF(
    λ(Func, λ(α, WellOrderedRecursion.recursiveFunctionOn(Func)(α)(membershipRelation(α))))
  )

  /**
   * The constructed function has domain `α` and satisfies the transfinite recurrence.
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
    val witness = WellOrderedRecursion.recursiveFunctionOn(Func)(α)(membershipRelation(α))
    val rec = transfiniteRecursionFunction(Func)(α)
    val recDefinition = transfiniteRecursionFunction.definition.of(Func := Func, α := α)
    val witnessSpec = have(
      functionOn(witness)(α) /\
        ∀(β ∈ α, witness(β) === Func(β)(witness ↾ initialSegment(β)(α)(membershipRelation(α))))
    ) by Tautology.from(
      ordinal.definition,
      WellOrderedRecursion.recursiveFunctionOnSpec.of(A := α, < := membershipRelation(α), Func := Func)
    )

    val witnessFunOn = have(functionOn(witness)(α)) by Weakening(witnessSpec)
    val recFunOn = have(functionOn(rec)(α)) by Congruence.from(witnessFunOn, recDefinition)
    val witnessEquations = have(
      ∀(β ∈ α, witness(β) === Func(β)(witness ↾ initialSegment(β)(α)(membershipRelation(α))))
    ) by Weakening(witnessSpec)
    val equation = have(β ∈ α |- rec(β) === Func(β)(rec ↾ β)) subproof {
      assume(β ∈ α)
      val witnessAtBeta = have(
        witness(β) === Func(β)(witness ↾ initialSegment(β)(α)(membershipRelation(α)))
      ) by InstantiateForall(β)(witnessEquations)
      have(thesis) by Congruence.from(witnessAtBeta, Ordinal.ordinalInitialSegment, recDefinition)
    }
    have(β ∈ α ==> (rec(β) === Func(β)(rec ↾ β))) by Restate.from(equation)
    val recEquations = thenHave(∀(β ∈ α, rec(β) === Func(β)(rec ↾ β))) by RightForall
    have(thesis) by RightAnd(recFunOn, recEquations)
  }

  /**
   * A function on `α` satisfying the transfinite recurrence exists.
   */
  val transfiniteRecursionWithFunctionOn = Theorem(
    ordinal(α) |- ∃(G, functionOn(G)(α) /\ ∀(β ∈ α, G(β) === Func(β)(G ↾ β)))
  ) {
    have(transfiniteRecursionFunctionSpec.statement) by Restate.from(transfiniteRecursionFunctionSpec)
    thenHave(thesis) by RightExists
  }

  /**
   * Transfinite recursion supplies a function satisfying the recurrence at every point of `α`.
   */
  val transfiniteRecursion = Theorem(
    ordinal(α) |- ∃(G, ∀(β ∈ α, G(β) === F(β)(G ↾ β)))
  ) {
    val rec = transfiniteRecursionFunction(F)(α)
    have(ordinal(α) |- ∀(β ∈ α, rec(β) === F(β)(rec ↾ β))) by
      Weakening(transfiniteRecursionFunctionSpec.of(Func := F))
    thenHave(thesis) by RightExists
  }
}
