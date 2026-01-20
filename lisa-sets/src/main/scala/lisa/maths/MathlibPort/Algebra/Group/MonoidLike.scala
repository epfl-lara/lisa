package lisa.maths.MathlibPort.Algebra.Group

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Group/Defs` (identity basics).
 *
 * This file contains a minimal set-based lemma about identity elements for a
 * binary operation `mul : (G × G) -> G`.
 */
object MonoidLike extends lisa.Main {

  val G = variable[Ind]
  val mul = variable[Ind]

  val e1 = variable[Ind]
  val e2 = variable[Ind]

  val x = variable[Ind]

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val leftId1 = forall(x, (x ∈ G) ==> ((e1 * x) === x))
  val rightId1 = forall(x, (x ∈ G) ==> ((x * e1) === x))
  val leftId2 = forall(x, (x ∈ G) ==> ((e2 * x) === x))
  val rightId2 = forall(x, (x ∈ G) ==> ((x * e2) === x))

  val identity_unique = Theorem(
    (e1 ∈ G, e2 ∈ G, leftId1, rightId1, leftId2, rightId2) |- (e1 === e2)
  ) {
    val `e1 ∈ G` = assume(e1 ∈ G)
    val `e2 ∈ G` = assume(e2 ∈ G)
    val l1 = assume(leftId1)
    val r2 = assume(rightId2)

    val s1 = have((e1 * e2) === e1) by Tautology.from(r2 of e1, `e1 ∈ G`)
    val s2 = have((e1 * e2) === e2) by Tautology.from(l1 of e2, `e2 ∈ G`)
    have(thesis) by Congruence.from(s1, s2)
  }
}
