package lisa.maths.SetTheory.Ordinals

import Ordinal._

/**
 * Definitions of ordinal arithmetic: addition, multiplication and exponentiation.
 */
object Arithmetic extends lisa.Main {

  /**
   * Embedding of Scala integers to ordinals by repeatedly applying `S`.
   *
   * Warning: this stack-overflows at around n = 1000. For larger numbers, a
   * better encoding is required.
   */
  private def toOrdinal(n: Int): Expr[Ind] = {
    if n < 0 then throw new IllegalArgumentException(s"Cannot convert negative integer $n to ordinal.")
    else if n == 0 then zero
    else S(toOrdinal(n - 1))
  }

  /**
   * For each integer `n`, generates a term with a definition that is printed as `n`.
   */
  // given Conversion[Int, Expr[Ind]] = n => DEF(using sourcecode.FullName(s"$n"))(toOrdinal(n)).printAs(_ => s"$n")
}
