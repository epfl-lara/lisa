package lisa.maths.MathlibPort.Algebra.Ring.CommRing

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}

/**
 * Basic projection theorems for [[Defs.commRing]].
 */
object BasicTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val commRing_isRing = Theorem(
    Defs.commRing(R)(add)(zero)(negOp)(mul)(one) |- RingDefs.ring(R)(add)(zero)(negOp)(mul)(one)
  ) {
    have(thesis) by Tautology.from(Defs.commRing.definition)
  }

  val commRing_mul_comm = Theorem(
    Defs.commRing(R)(add)(zero)(negOp)(mul)(one) |- RingDefs.commutativeMul(R)(mul)
  ) {
    have(thesis) by Tautology.from(Defs.commRing.definition)
  }
}
