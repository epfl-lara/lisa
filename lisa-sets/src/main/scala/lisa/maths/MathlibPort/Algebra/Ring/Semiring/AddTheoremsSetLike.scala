package lisa.maths.MathlibPort.Algebra.Ring.Semiring

import lisa.maths.MathlibPort.Algebra.Ring.AddGroupTheoremsSetLike
import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Additive theorems derived from [[Defs.semiring]] (via `addCommMonoid`).
 */
object AddTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  extension (a: Expr[Ind]) {
    infix def +(b: Expr[Ind]): Expr[Ind] = addApp(a, b)
  }

  val addCommMonoid_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.addCommMonoid(R)(add)(zero)
  ) {
    have(thesis) by Tautology.from(BasicTheoremsSetLike.semiring_addCommMonoid)
  }

  val addMonoid_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.addMonoid(R)(add)(zero)
  ) {
    have(thesis) by Tautology.from(addCommMonoid_of_semiring, RingDefs.addCommMonoid.definition)
  }

  val hasAdd_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.hasAdd(R)(add)
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))

    have(RingDefs.addMonoid(R)(add)(zero)) by Tautology.from(addMonoid_of_semiring, s)
    have(RingDefs.addSemigroup(R)(add)) by Tautology.from(RingDefs.addMonoid.definition, lastStep)
    have(RingDefs.hasAdd(R)(add)) by Tautology.from(RingDefs.addSemigroup.definition, lastStep)

    have(thesis) by Tautology.from(lastStep)
  }

  val zero_mem_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- zero ∈ R
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    have(RingDefs.addMonoid(R)(add)(zero)) by Tautology.from(addMonoid_of_semiring, s)
    have(thesis) by Tautology.from(AddGroupTheoremsSetLike.zero_mem_of_addMonoid of (R := R, add := add, zero := zero), lastStep)
  }

  val add_closed_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- (x + y) ∈ R
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    have(RingDefs.hasAdd(R)(add)) by Tautology.from(hasAdd_of_semiring, s)
    have(thesis) by Tautology.from(AddGroupTheoremsSetLike.add_closed of (R := R, add := add, x := x, y := y), lastStep, hx, hy)
  }

  val zero_add_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- ((zero + x) === x)
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)

    have(RingDefs.addMonoid(R)(add)(zero)) by Tautology.from(addMonoid_of_semiring, s)
    val leftZero = have(forall(x, (x ∈ R) ==> ((zero + x) === x))) by Tautology.from(
      AddGroupTheoremsSetLike.left_zero_of_addMonoid of (R := R, add := add, zero := zero),
      lastStep
    )
    have(thesis) by Tautology.from(leftZero of x, hx)
  }

  val add_zero_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R) |- ((x + zero) === x)
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)

    have(RingDefs.addMonoid(R)(add)(zero)) by Tautology.from(addMonoid_of_semiring, s)
    val rightZero = have(forall(x, (x ∈ R) ==> ((x + zero) === x))) by Tautology.from(
      AddGroupTheoremsSetLike.right_zero_of_addMonoid of (R := R, add := add, zero := zero),
      lastStep
    )
    have(thesis) by Tautology.from(rightZero of x, hx)
  }

  val add_assoc_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R, z ∈ R) |- (((x + y) + z) === (x + (y + z)))
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)
    val hz = assume(z ∈ R)

    have(RingDefs.addMonoid(R)(add)(zero)) by Tautology.from(addMonoid_of_semiring, s)
    have(RingDefs.addSemigroup(R)(add)) by Tautology.from(RingDefs.addMonoid.definition, lastStep)
    have(RingDefs.associativeAdd(R)(add)) by Tautology.from(RingDefs.addSemigroup.definition, lastStep)
    thenHave(
      forall(
        x,
        (x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) + z) === (x + (y + z)))))
      )
    ) by Substitute(RingDefs.associativeAdd.definition of (R := R, add := add))

    val assocAtX = have((x ∈ R) ==> forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) + z) === (x + (y + z)))))) by Tautology.from(
      lastStep of x
    )
    val assocAtXForallY = have(forall(y, (y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) + z) === (x + (y + z)))))) by Tautology.from(assocAtX, hx)
    val assocAtXY = have((y ∈ R) ==> forall(z, (z ∈ R) ==> (((x + y) + z) === (x + (y + z))))) by Tautology.from(assocAtXForallY of y)
    val assocAtXYForallZ = have(forall(z, (z ∈ R) ==> (((x + y) + z) === (x + (y + z))))) by Tautology.from(assocAtXY, hy)
    val assocAtXYZ = have((z ∈ R) ==> (((x + y) + z) === (x + (y + z)))) by Tautology.from(assocAtXYForallZ of z)

    have(thesis) by Tautology.from(assocAtXYZ, hz)
  }

  val add_comm_of_semiring = Theorem(
    (Defs.semiring(R)(add)(zero)(mul)(one), x ∈ R, y ∈ R) |- ((x + y) === (y + x))
  ) {
    val s = assume(Defs.semiring(R)(add)(zero)(mul)(one))
    val hx = assume(x ∈ R)
    val hy = assume(y ∈ R)

    have(RingDefs.addCommMonoid(R)(add)(zero)) by Tautology.from(addCommMonoid_of_semiring, s)
    have(RingDefs.commutativeAdd(R)(add)) by Tautology.from(RingDefs.addCommMonoid.definition, lastStep)
    thenHave(forall(x, (x ∈ R) ==> forall(y, (y ∈ R) ==> ((x + y) === (y + x))))) by Substitute(
      RingDefs.commutativeAdd.definition of (R := R, add := add)
    )

    val commAtX = have((x ∈ R) ==> forall(y, (y ∈ R) ==> ((x + y) === (y + x)))) by Tautology.from(lastStep of x)
    val commAtXForallY = have(forall(y, (y ∈ R) ==> ((x + y) === (y + x)))) by Tautology.from(commAtX, hx)
    val commAtXY = have((y ∈ R) ==> ((x + y) === (y + x))) by Tautology.from(commAtXForallY of y)

    have(thesis) by Tautology.from(commAtXY, hy)
  }
}

