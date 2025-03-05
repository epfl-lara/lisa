package lisa.maths.settheory

import lisa.maths.settheory.UnorderedPair.*
import lisa.maths.settheory.Singleton.*

object Pair extends lisa.Main:

  private val s = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val p = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Ind >>: Prop]

  /**
   * An ordered pair.
   */
  val pair = DEF(lambda(x, lambda(y, ~x <> (x <> y))))

  extension (t: Expr[Ind]) infix def ::(s: Expr[Ind]) = pair(t)(s)

  // val firstMemberExists = Theorem(exists(x, exists(y, p === x :: y)) ==> exists(y, p === x :: y)):
  //   have(p === x :: y |- p === x :: y) by Restate
  //   thenHave(p === x :: y |- exists(y, p === x :: y)) by Restate

  // // first of a pair
  // val first = DEF( lambda(p, ε(x, exists(x, exists(y, p === x :: y)) ==> exists(y, p === x :: y))) )

  // // second of a pair
  // val second = DEF( lambda(p, ε(y, exists(x, exists(y, p === x :: y)) ==> exists(x, p === x :: y))) )

  // val firstExists = Theorem(exists(x, exists(x, exists(y, p === x :: y)) ==> exists(y, p === x :: y))):
  //   have(p === x :: y |- p === x :: y) by Restate
  //   thenHave(p === x :: y |- exists(y, p === x :: y)) by RightExists

end Pair
