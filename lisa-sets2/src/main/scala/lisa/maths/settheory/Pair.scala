package lisa.maths.settheory

import lisa.maths.settheory.UnorderedPair.*
import lisa.maths.settheory.Singleton.*

object Pair extends lisa.Main:

  private val s = variable[Term]
  private val x = variable[Term]
  private val y = variable[Term]
  private val z = variable[Term]
  private val p = variable[Term]
  private val P = variable[Term >>: Formula]
  private val Q = variable[Term >>: Term >>: Formula]

  /**
    * An ordered pair.
    */
  val pair = DEF ( lambda(x, lambda(y, ~x <> (x <> y))) )

  // extension (t: Term)
  //   infix def :: (s: Term) = pair(t)(s)

  // val firstMemberExists = Theorem(exists(x, exists(y, p === x :: y)) ==> exists(y, p === x :: y)):
  //   have(p === x :: y |- p === x :: y) by Restate
  //   thenHave(p === x :: y |- exists(y, p === x :: y)) by Restate

  // // first of a pair
  // val first = EpsilonDEF( lambda(p, ε(x, exists(x, exists(y, p === x :: y)) ==> exists(y, p === x :: y))) )

  // // second of a pair
  // val second = EpsilonDEF( lambda(p, ε(y, exists(x, exists(y, p === x :: y)) ==> exists(x, p === x :: y))) )

end Pair
