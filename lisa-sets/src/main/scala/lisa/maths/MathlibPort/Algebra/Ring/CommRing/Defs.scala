package lisa.maths.MathlibPort.Algebra.Ring.CommRing

import lisa.maths.MathlibPort.Algebra.Ring.Defs as RingDefs
import lisa.maths.SetTheory.Base.Predef.{_, given}

/**
 * Commutative ring predicate (fragment).
 */
object Defs extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]

  val commRing = DEF(
    λ(
      R,
      λ(
        add,
        λ(
          zero,
          λ(
            negOp,
            λ(mul, λ(one, RingDefs.ring(R)(add)(zero)(negOp)(mul)(one) /\ RingDefs.commutativeMul(R)(mul)))
          )
        )
      )
    )
  )
}
