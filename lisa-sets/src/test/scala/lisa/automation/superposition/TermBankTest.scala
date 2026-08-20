package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core._

/**
 * `TermBank.varsOf`, whose two paths must agree.
 *
 * A term's free variables are read off its cached mask, one bit per variable number, which is why the query
 * costs no traversal. But the mask has only 64 bits, and everything from variable 63 upward collapses into one
 * overflow bit that names no number, so those variables have to be walked for. That second path is what these
 * tests are for: nothing in the rest of the suite builds a clause with 63 variables, and a prover run will not
 * either, since the `Applier` renumbers each conclusion's variables densely from zero.
 *
 * Getting it wrong is not a crash but a silently wrong answer, and the callers turn a wrong answer into an
 * unsound demodulator (one whose right-hand side introduces a variable the left does not bind) or a proof step
 * whose substitution misses part of its domain.
 */
class TermBankTest extends AnyFunSuite:

  /**
   * The variable numbers of `ts`, sorted, so a test can state the expected set without fixing the order --
   * which `varsOf` deliberately does not promise across the mask and overflow parts of its answer.
   */
  private def nums(f: TermFixture, ts: Array[Term]): Seq[Int] = ts.map(f.bank.varNum(_).num).toSeq.sorted

  test("a ground term has no variables") {
    val f = new TermFixture
    val g = f.fn("g", 1)
    assert(f.bank.varsOf(f.app(g, f.const("a"))).isEmpty)
    assert(f.bank.varsOf(f.clause(f.pos(f.app(f.pred("p", 1), f.const("a"))))).isEmpty)
  }

  test("variables below the overflow bit come straight from the mask, deduplicated") {
    val f = new TermFixture
    val g = f.fn("g", 2)
    // g(x0, g(x2, x0)): x0 twice, and the nesting means a wrong answer could double-count or miss it
    val t = f.app(g, f.v(0), f.app(g, f.v(2), f.v(0)))
    assert(nums(f, f.bank.varsOf(t)) == Seq(0, 2))
  }

  test("a variable at or above 63 is found by the traversal fallback") {
    val f = new TermFixture
    val g = f.fn("g", 2)
    // 63 is the first number the mask cannot name: `varBit` maps it, and everything above, to the overflow bit
    assert(nums(f, f.bank.varsOf(f.v(63))) == Seq(63))
    assert(nums(f, f.bank.varsOf(f.app(g, f.v(1), f.v(70)))) == Seq(1, 70))
    // two distinct high variables share the one overflow bit, so only the walk can tell them apart
    assert(nums(f, f.bank.varsOf(f.app(g, f.v(70), f.v(99)))) == Seq(70, 99))
    // and a repeated high variable must still come out once
    assert(nums(f, f.bank.varsOf(f.app(g, f.v(70), f.app(g, f.v(70), f.v(4))))) == Seq(4, 70))
  }

  test("the clause form unions its literals, on both paths") {
    val f = new TermFixture
    val p = f.pred("p", 1)
    val q = f.pred("q", 2)
    val low = f.clause(f.pos(f.app(p, f.v(0))), f.neg(f.app(q, f.v(3), f.v(0))))
    assert(nums(f, f.bank.varsOf(low)) == Seq(0, 3))
    // the overflow bit set by one literal must not stop the others' variables being reported
    val high = f.clause(f.pos(f.app(p, f.v(80))), f.neg(f.app(q, f.v(2), f.v(80))), f.pos(f.app(p, f.v(64))))
    assert(nums(f, f.bank.varsOf(high)) == Seq(2, 64, 80))
  }

  test("varsSubsetOf decides containment from the masks, and by hand above the overflow bit") {
    val f = new TermFixture
    val g = f.fn("g", 2)
    val gx0x2 = f.app(g, f.v(0), f.v(2))
    assert(f.bank.varsSubsetOf(f.v(0), gx0x2))
    assert(!f.bank.varsSubsetOf(gx0x2, f.v(0)))
    assert(f.bank.varsSubsetOf(f.const("a"), f.v(0)), "a ground term's (empty) variable set is a subset of any")
    // the case the mask alone gets wrong: two *different* high variables set the same one overflow bit, so a
    // plain `(ma & mb) == ma` would report containment where there is none
    assert(!f.bank.varsSubsetOf(f.v(70), f.v(99)))
    assert(f.bank.varsSubsetOf(f.v(70), f.app(g, f.v(70), f.v(99))))
    assert(!f.bank.varsSubsetOf(f.app(g, f.v(1), f.v(70)), f.app(g, f.v(1), f.v(99))))
  }

  test("varsOf agrees with containsVar, the other reader of the same mask") {
    val f = new TermFixture
    val g = f.fn("g", 2)
    val t = f.app(g, f.v(5), f.app(g, f.v(64), f.v(5)))
    val found = nums(f, f.bank.varsOf(t)).toSet
    // every variable `varsOf` reports must be one `containsVar` confirms, and no other in range
    for n <- 0 to 70 do assert(f.bank.containsVar(t, Core.Variable(n)) == found.contains(n), s"disagreement on variable $n")
  }
