package lisa.maths.MathlibPort.Algebra.Ring.Semiring

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}

/**
 * Basic projection theorems for [[Defs.semiring]].
 */
object BasicTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val semiring_addCommMonoid = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.addCommMonoid(R)(add)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val semiring_mulMonoid = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.mulMonoid(R)(mul)(one)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val semiring_distrib = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- RingDefs.distrib(R)(add)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val mulZero_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- Defs.mulZero(R)(mul)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }

  val zeroMul_of_semiring = Theorem(
    Defs.semiring(R)(add)(zero)(mul)(one) |- Defs.zeroMul(R)(mul)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.semiring.definition)
  }
}
