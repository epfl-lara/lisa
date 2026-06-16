package lisa.hol

import lisa.hol.VarsAndFunctions._
import org.scalatest.funsuite.AnyFunSuite

/**
 * Test suite for HOL expression construction and type-checking,
 * corresponding to [[lisa.hol.HOLTest]].
 */
class HOLTestSuite extends HOLTestMain {

  val x = typedvar(𝔹)
  val y = typedvar(𝔹)
  val f = typedvar(𝔹 ->: 𝔹)
  val g = typedvar(𝔹 ->: (𝔹 ->: 𝔹))
  val h = typedvar((𝔹 ->: 𝔹) ->: 𝔹)

  val expr1 = g * (x) * (f * (y))
  assert(computeType(expr1) == 𝔹)
  val typecheckTest = TypingTheorem(expr1 :: 𝔹)

  val expr2 = g * (x) * (fun(x :: 𝔹, f * (x)) * (y))
  assert(computeType(expr2) == 𝔹)
  val typecheckTest2 = TypingTheorem(expr2 :: 𝔹)

  val expr3 = x =:= y
  assert(computeType(expr3) == 𝔹)
  val typecheckTest3 = TypingTheorem(expr3 :: 𝔹)

  val expr4 = (g * (x)) =:= fun(x :: 𝔹, f * (x))
  assert(computeType(expr4) == 𝔹)
  val typecheckTest4 = TypingTheorem(expr4 :: 𝔹)

  val expr5 = fun(h :: ((𝔹 ->: 𝔹) ->: 𝔹), fun(f :: (𝔹 ->: 𝔹), f * (x)) =:= h)
  assert(computeType(expr5) == (((𝔹 ->: 𝔹) ->: 𝔹) ->: 𝔹))
  val typecheckTest5 = TypingTheorem(expr5 :: (((𝔹 ->: 𝔹) ->: 𝔹) ->: 𝔹))

}
