package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*
import Oracles.*
import lisa.automation.superposition.ordering.*

/**
 * Tests for the equality-aware [[Order]]: orientation, the literal order `≻_L`
 * (equality multiset + resolution order + equality-below-non-equality), (strict) maximality, and the
 * clause order `≻_C`. Terms are built directly through a [[Signature]] + [[TermBank]] (as in [[KBOTest]]);
 * constants interned earlier have lower precedence, so `const("a") < const("b") < const("c")`.
 */
class OrderTest extends AnyFunSuite:

  class Fix extends TermFixture

  import Cmp.*

  // --- orientation --------------------------------------------------------------------------------

  test("orientation: the heavier side is greater; equal/incomparable sides are unoriented") {
    val fx = new Fix; import fx.*
    val a = const("a"); val f = fn("f", 1)
    assert(order.orient(mkEq(app(f, a), a)) == Gt) // f(a) ≻ a
    assert(order.orient(mkEq(a, app(f, a))) == Lt)
    assert(order.orient(mkEq(a, a)) == Eq)
    assert(order.orient(mkEq(v(0), v(1))) == Inc) // x = y : incomparable
    assert(order.maximalSide(mkEq(app(f, a), a)).contains(app(f, a)))
    assert(order.maximalSide(mkEq(v(0), v(1))).isEmpty)
  }

  /**
   * The orientation memo must not outlive the ordering it was computed under. Weights are fixed when a symbol
   * is interned, so the only thing that can change the ordering once terms exist is [[Precedence.assign]],
   * which runs after the clauses are built and clears the memo as its last act.
   *
   * Here `a`/`b` are equal-weight constants, so their orientation is decided by precedence alone.
   */
  test("Precedence.assign drops orientation verdicts taken before it ran") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b") // interned in order ⇒ precedence a < b
    val eq = mkEq(a, b)
    assert(order.orient(eq) == Lt) // a ≺ b under the interning order, and now memoised
    // `InvFrequency` puts the *more frequent* symbol lower, and this clause set mentions `b` twice, so the
    // assignment reverses the two and the memoised verdict is no longer the right one.
    Precedence.assign(sig, bank, Seq(clause(pos(mkEq(b, b))), clause(pos(mkEq(a, b)))), PrecedenceScheme.InvFrequency)
    assert(sig.info(fn("a", 0)).precedence > sig.info(fn("b", 0)).precedence, "expected the assignment to flip a/b")
    assert(order.orient(eq) == Gt, "orient returned a verdict cached under the pre-assignment precedence")
  }

  // --- equality literal order (multiset extension) ------------------------------------------------

  test("equality literal order: larger side dominates, and a negative outranks a positive it dominates") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val c = const("c") // a ≺ b ≺ c
    val s = c; val t = b; val u = a // s ≻ t ≻ u
    // {c,b} vs {c,a} : cancel c, then b ≻ a  ⇒  (s = t) ≻ (s = u)
    assert(order.compareLit(lit(mkEq(s, t), true), lit(mkEq(s, u), true)) == Gt)
    // negative ≻ positive on the SAME terms: {c,c,b,b} vs {c,b} ⇒ Gt
    assert(order.compareLit(lit(mkEq(s, t), false), lit(mkEq(s, t), true)) == Gt)
    // the duplicated sides let a negative outrank a positive with a smaller atom:
    // (s ≠ u) : {c,c,a,a} vs (s = t) : {c,b} ⇒ cancel one c, leftover {c,a,a} dominates {b} (c ≻ b) ⇒ Gt
    assert(order.compareLit(lit(mkEq(s, u), false), lit(mkEq(s, t), true)) == Gt)
  }

  test("specialized equality comparison agrees with the generic multiset oracle (randomized)") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b")
    val f = fn("f", 1); val g = fn("g", 2)
    val x = v(0); val y = v(1)
    // ground + variable terms with shared structure, to exercise cancellation and incomparability
    val pool: Array[Term] = Array(
      a, b, x, y,
      app(f, a), app(f, b), app(f, x), app(f, y),
      app(g, a, b), app(g, x, y), app(g, a, x), app(g, x, a)
    )
    // the reference encoding: positive → {s,t}, negative → {s,s,t,t} (Bachmair-Ganzinger, doubled)
    def sides(s: Term, t: Term, pos: Boolean): Array[Term] = if pos then Array(s, t) else Array(s, s, t, t)
    val rng = new scala.util.Random(20260713L)
    var iters = 0
    while iters < 5000 do
      val s = pool(rng.nextInt(pool.length)); val t = pool(rng.nextInt(pool.length))
      val u = pool(rng.nextInt(pool.length)); val vv = pool(rng.nextInt(pool.length))
      val p1 = rng.nextBoolean(); val p2 = rng.nextBoolean()
      val expected = order.termMultisetCompare(sides(s, t, p1), sides(u, vv, p2)) // generic oracle
      val got = order.compareLit(lit(mkEq(s, t), p1), lit(mkEq(u, vv), p2)) //        specialized path
      assert(got == expected, s"mismatch on (${s},${t})$p1 vs (${u},${vv})$p2: specialized=$got oracle=$expected")
      iters += 1
  }

  test("symmetric equalities are order-equal; distinct-variable sides are incomparable") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val f = fn("f", 1)
    assert(order.compareLit(lit(mkEq(a, b), true), lit(mkEq(b, a), true)) == Eq) // {a,b} == {b,a}
    // {f(x),a} vs {f(y),a} : cancel a, then f(x) vs f(y) incomparable ⇒ Inc
    assert(order.compareLit(lit(mkEq(app(f, v(0)), a), true), lit(mkEq(app(f, v(1)), a), true)) == Inc)
  }

  // --- level rule + non-equality (resolution) behaviour -------------------------------------------

  test("equality literals rank below non-equality literals") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val P = pred("P", 1)
    assert(order.compareLit(lit(app(P, a), true), lit(mkEq(a, b), true)) == Gt) // P(a) ≻ (a=b)
    assert(order.compareLit(lit(mkEq(a, b), true), lit(app(P, a), true)) == Lt)
    assert(order.compareLit(lit(mkEq(a, b), false), lit(app(P, a), true)) == Lt) // even a NEG equality is below a POS non-eq
  }

  test("non-equality literals keep the resolution order (heavier atom; negative on a tie; precedence)") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b")
    val P = pred("P", 1); val Q = pred("Q", 1) // prec(P) < prec(Q)
    val f = fn("f", 1)
    assert(order.compareLit(lit(app(P, app(f, a)), true), lit(app(P, a), true)) == Gt) // P(f(a)) ≻ P(a)
    assert(order.compareLit(lit(app(P, a), false), lit(app(P, a), true)) == Gt) //          ¬P(a) ≻ P(a)
    assert(order.compareLit(lit(app(P, a), true), lit(app(Q, a), true)) == Lt) //           P(a) ≺ Q(a) by precedence
    val _ = b
  }

  // --- maximality ---------------------------------------------------------------------------------

  test("maximality vs strict maximality: order-equal duplicates are maximal but not strictly maximal") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b")
    val lits = Array(lit(mkEq(a, b), true), lit(mkEq(b, a), true)) // two ≻_L-equal (symmetric) literals
    assert(order.isMaximal(lits, 0) && order.isMaximal(lits, 1))
    assert(!order.isStrictlyMaximal(lits, 0) && !order.isStrictlyMaximal(lits, 1)) // Eq to each other ⇒ not strict
  }

  test("an incomparable pair is jointly maximal; a dominated literal is neither maximal nor strict") {
    val fx = new Fix; import fx.*
    val a = const("a"); val f = fn("f", 1)
    val incPair = Array(lit(mkEq(app(f, v(0)), a), true), lit(mkEq(app(f, v(1)), a), true)) // Inc to each other
    assert(order.isMaximal(incPair, 0) && order.isMaximal(incPair, 1)) // Inc never demotes
    val P = pred("P", 1)
    val clause = Array(lit(app(P, app(f, a)), true), lit(app(P, a), true)) // P(f(a)) ≻ P(a)
    assert(order.isMaximal(clause, 0) && order.isStrictlyMaximal(clause, 0)) // the heavy literal is strictly maximal
    assert(!order.isMaximal(clause, 1)) //                                    the light one is dominated
    assert(order.maximalFlags(clause).sameElements(Array(true, false)))
  }

  // --- clause order -------------------------------------------------------------------------------

  test("clause order: a superset clause is greater; symmetric-equality clauses are equal") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b")
    val P = pred("P", 1); val Q = pred("Q", 1); val f = fn("f", 1)
    val pq = bank.mkClause(Array(lit(app(P, a), true), lit(app(Q, a), true)))
    val p = bank.mkClause(Array(lit(app(P, a), true)))
    assert(order.compareClause(pq, p) == Gt) // {P(a),Q(a)} ≻ {P(a)}
    assert(order.compareClause(p, pq) == Lt)
    val heavy = bank.mkClause(Array(lit(app(P, app(f, a)), true)))
    assert(order.compareClause(heavy, p) == Gt) // {P(f(a))} ≻ {P(a)}
    val e1 = bank.mkClause(Array(lit(mkEq(a, b), true)))
    val e2 = bank.mkClause(Array(lit(mkEq(b, a), true)))
    assert(order.compareClause(e1, e2) == Eq) // {a=b} == {b=a}
  }

  // --- selector regression (equality-free behaviour unchanged) ------------------------------------

  test("the BG-complete selector still selects the negative literal on an equality-free clause") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b")
    val P = pred("P", 1); val Q = pred("Q", 1)
    val sel = new CompleteBestLiteralSelector(order)
    val lits = Array(lit(app(P, a), false), lit(app(Q, b), true)) // ¬P(a) ∨ Q(b)
    assert(sel.select(bank, lits).sameElements(Array(0))) // selects the negative ¬P(a)
  }
