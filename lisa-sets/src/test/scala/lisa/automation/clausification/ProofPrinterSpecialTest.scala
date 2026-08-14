package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.tptp.ProofPrinter

/** Checks that `ProofPrinter.formulaToFOFFormula` (strict) prints ε-terms, TPTP distinct objects, and numerals
 *  correctly: the cases that used to throw or be mis-rendered. */
class ProofPrinterSpecialTest extends AnyFunSuite:

  private def pretty(e: K.Expression): String =
    ProofPrinter.formulaToFOFFormula(e, Set.empty, strict = true).pretty

  private val q = Constant(Identifier("q"), Ind >>: Prop) // a unary predicate to sit the term under
  private val p = Constant(Identifier("p"), Ind >>: Prop)

  test("ε-terms print with leo's term-level epsilon binder `#` (no longer throws)") {
    val x = Variable(Identifier("X0"), Ind)
    val eps = epsilon(Lambda(x, p(x))) //          ε X0. p(X0)   (an Ind term)
    val s = pretty(q(eps)) //                      q(ε X0. p(X0))
    assert(s.contains("#"), s"expected epsilon binder `#` in: $s")
    assert(s.contains("p(X0)"), s"expected the body in: $s")
  }

  test("TPTP distinct objects print as \"...\" and numerals as bare numbers") {
    val d = Constant(Identifier("$dfoo$ubar"), Ind) //   KernelParser's parking of the distinct object "foo_bar"
    val n = Constant(Identifier("$n42"), Ind) //         ... of the numeral 42
    val real = Constant(Identifier("$n3.14"), Ind) //    a real literal (fallback path)
    assert(pretty(q(d)).contains("\"foo_bar\""), pretty(q(d)))
    assert(pretty(q(n)).contains("(42)") || pretty(q(n)).endsWith("42)"), pretty(q(n)))
    assert(!pretty(q(n)).contains("$n"), pretty(q(n)))
    // real degrades to a valid (escaped) atomic word, never `$n`
    assert(!pretty(q(real)).contains("$n"), pretty(q(real)))
  }
