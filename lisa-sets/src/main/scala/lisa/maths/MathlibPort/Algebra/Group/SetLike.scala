package lisa.maths.MathlibPort.Algebra.Group

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Group/Basic` (set-based layer).
 *
 * This file introduces a set-based "hasMul" predicate: a binary operation is a
 * function `mul : (G × G) -> G`. This is the bridge from the untyped operation
 * layer to carrier-based algebraic structures.
 */
object SetLike extends lisa.Main {

  val G = variable[Ind]
  val mul = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]

  extension (a: Expr[Ind]) {
    infix def *(b: Expr[Ind]): Expr[Ind] = Functions.Function.app(mul)((a, b))
  }

  // Re-export (do NOT re-DEF): global `DEF` symbols must be unique across the whole JVM.
  val hasMul = Defs.hasMul

  val mul_closed = Theorem(
    (mul :: (G × G) -> G, x ∈ G, y ∈ G) |- (x * y) ∈ G
  ) {
    assume(mul :: (G × G) -> G)
    assume(x ∈ G)
    assume(y ∈ G)

    have((x, y) ∈ (G × G)) by Tautology.from(CartesianProduct.membershipSufficientCondition of (A := G, B := G))
    have((x * y) ∈ G) by Tautology.from(
      Functions.BasicTheorems.appTyping of (f := mul, A := (G × G), B := G, x := (x, y)),
      lastStep
    )
  }
}
