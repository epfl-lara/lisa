package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Distributivity lemmas for the ring-like predicates in [[Defs]].
 */
object DistribTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def mulApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  extension (a: Expr[Ind]) {
    infix def +(b: Expr[Ind]): Expr[Ind] = addApp(a, b)
    infix def *(b: Expr[Ind]): Expr[Ind] = mulApp(a, b)
  }

  val left_distrib_of_ring = Theorem(
    Defs.ring(R)(add)(zero)(negOp)(mul)(one) |- Defs.leftDistrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.ring.definition, Defs.distrib.definition)
  }

  val right_distrib_of_ring = Theorem(
    Defs.ring(R)(add)(zero)(negOp)(mul)(one) |- Defs.rightDistrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.ring.definition, Defs.distrib.definition)
  }

  val mul_add = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (x * (y + z)) === ((x * y) + (x * z))
  ) {
    val r = assume(Defs.ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)

    have(Defs.leftDistrib(R)(add)(mul)) by Tautology.from(left_distrib_of_ring, r)
    thenHave(
      forall(x, (x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))))
    ) by Substitute(Defs.leftDistrib.definition of (R := R, add := add, mul := mul))
    val distAtX = have((x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z)))))) by Tautology.from(
      lastStep of x
    )
    val distAtXForallY = have(forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z)))))) by Tautology.from(distAtX, hx)
    val distAtXY = have((y ∈ R) ==> forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))) by Tautology.from(distAtXForallY of y)
    val distAtXYForallZ = have(forall(z, (z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z))))) by Tautology.from(distAtXY, hy)
    val distAtXYZ = have((z ∈ R) ==> ((x * (y + z)) === ((x * y) + (x * z)))) by Tautology.from(distAtXYForallZ of z)

    have(thesis) by Tautology.from(distAtXYZ, hz)
  }

  val add_mul = Theorem(
    (Defs.ring(R)(add)(zero)(negOp)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (((x + y) * z) === ((x * z) + (y * z)))
  ) {
    val r = assume(Defs.ring(R)(add)(zero)(negOp)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)

    have(Defs.rightDistrib(R)(add)(mul)) by Tautology.from(right_distrib_of_ring, r)
    thenHave(
      forall(x, (x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> ((((x + y) * z) === ((x * z) + (y * z)))))))
    ) by Substitute(Defs.rightDistrib.definition of (R := R, add := add, mul := mul))
    val distAtX = have(
      (x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z)))))
    ) by Tautology.from(lastStep of x)
    val distAtXForallY = have(
      forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z)))))
    ) by Tautology.from(distAtX, hx)
    val distAtXY = have((y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z))))) by Tautology.from(distAtXForallY of y)
    val distAtXYForallZ = have(forall(z, (z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z))))) by Tautology.from(distAtXY, hy)
    val distAtXYZ = have((z ∈ R) ==> (((x + y) * z) === ((x * z) + (y * z)))) by Tautology.from(distAtXYForallZ of z)

    have(thesis) by Tautology.from(distAtXYZ, hz)
  }
}
