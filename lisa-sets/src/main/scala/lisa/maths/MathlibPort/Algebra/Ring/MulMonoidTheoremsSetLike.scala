package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Set-based multiplicative-monoid theorems for the predicates in [[Defs]].
 */
object MulMonoidTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val hasMul_of_mulMonoid = Theorem(
    Defs.mulMonoid(R)(mul)(one) |- Defs.hasMul(R)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.mulMonoid.definition, Defs.mulSemigroup.definition)
  }

  val one_mem_of_mulMonoid = Theorem(
    Defs.mulMonoid(R)(mul)(one) |- one ∈ R
  ) {
    have(thesis) by Tautology.from(Defs.mulMonoid.definition, Defs.hasOne.definition)
  }

  val mul_closed = Theorem(
    (Defs.hasMul(R)(mul), x ∈ R, y ∈ R) |- (x * y) ∈ R
  ) {
    have(thesis) by Tautology.from(
      Defs.hasMul.definition,
      Functions.BasicTheorems.appTyping of (f := mul, A := (R × R), B := R, x := (x, y)),
      CartesianProduct.membershipSufficientCondition of (A := R, B := R, x := x, y := y)
    )
  }

  val one_mul_of_mulMonoid = Theorem(
    Defs.mulMonoid(R)(mul)(one) |- forall(x, (x ∈ R) ==> ((one * x) === x))
  ) {
    have(thesis) by Tautology.from(Defs.mulMonoid.definition, Defs.leftOne.definition)
  }

  val mul_one_of_mulMonoid = Theorem(
    Defs.mulMonoid(R)(mul)(one) |- forall(x, (x ∈ R) ==> ((x * one) === x))
  ) {
    have(thesis) by Tautology.from(Defs.mulMonoid.definition, Defs.rightOne.definition)
  }
}

