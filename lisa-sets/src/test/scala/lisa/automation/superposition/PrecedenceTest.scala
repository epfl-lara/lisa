package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Phase-5 heuristics: KBO symbol-**precedence** generation ([[Precedence]] / [[PrecedenceScheme]]). Checks the
 *  schemes produce a *total* order (KBO needs it), are deterministic, order symbols as advertised, and — most
 *  importantly — do not change the prover's verdict (an A/B against the former occurrence-order baseline). */
class PrecedenceTest extends AnyFunSuite:

  class Fix extends TermFixture:

    bank.selector = new CompleteBestLiteralSelector(bank.order)

    def precOf(f: Symbol): Int = sig.info(f).precedence
    def allPrecedences: Seq[Int] = sig.symbols.map(_.precedence).toSeq

  // ── totality: KBO returns Inc on equal precedence, so every scheme must assign DISTINCT ranks ────

  test("every scheme yields a total order (all precedences distinct, a permutation of 0..n-1)") {
    for scheme <- PrecedenceScheme.values do
      val fx = new Fix; import fx.*
      val f = fn("f", 1); val g = fn("g", 2); val a = const("a"); val b = const("b"); val P = pred("P", 1)
      val cs = Seq(clause(pos(app(P, app(f, a))), neg(mkEq(app(g, a, b), b))), clause(pos(mkEq(app(f, a), a))))
      Precedence.assign(sig, bank, cs, scheme)
      val precs = allPrecedences
      assert(precs.distinct.size == precs.size, s"$scheme produced duplicate precedences: $precs")
      assert(precs.sorted == (0 until precs.size).toList, s"$scheme is not a 0..n-1 permutation: ${precs.sorted}")
  }

  test("assignment is deterministic (same input ⇒ same precedences)") {
    def run(): Seq[Int] =
      val fx = new Fix; import fx.*
      val f = fn("f", 1); val g = fn("g", 1); val a = const("a")
      val cs = Seq(clause(pos(mkEq(app(f, app(f, a)), a))), clause(neg(mkEq(app(g, a), a))))
      Precedence.assign(sig, bank, cs, PrecedenceScheme.InvFrequency)
      sig.symbols.map(i => (i.name, i.arity, i.precedence)).toSeq.map(_._3)
    assert(run() == run())
  }

  // ── the schemes order symbols as documented ─────────────────────────────────────────────────────

  test("Occurrence reproduces the interning order (precedence == id)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val a = const("a")
    Precedence.assign(sig, bank, Seq(clause(pos(mkEq(app(f, a), app(g, a))))), PrecedenceScheme.Occurrence)
    assert(sig.symbols.forall(i => i.precedence == i.id.code))
  }

  test("InvFrequency: frequent symbols get smaller precedence, constants are minimal") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val b = const("b")
    // f occurs 3×, g once; a occurs a lot, b once. (unary f/g are non-constants; a/b are constants)
    val cs = Seq(
      clause(pos(mkEq(app(f, a), a))), //          f, a, a
      clause(pos(mkEq(app(f, app(f, a)), b))), //  f, f, a, b
      clause(neg(mkEq(app(g, a), a)))  //          g, a, a
    )
    Precedence.assign(sig, bank, cs, PrecedenceScheme.InvFrequency)
    assert(precOf(f) < precOf(g), "the more frequent unary f should rank below g")
    // both constants rank below both non-constant function symbols (const-min band)
    val aS = fn("a", 0); val bS = fn("b", 0)
    assert(precOf(aS) < precOf(f) && precOf(aS) < precOf(g), "constant a must be below the function symbols")
    assert(precOf(bS) < precOf(f) && precOf(bS) < precOf(g), "constant b must be below the function symbols")
    assert(precOf(aS) < precOf(bS), "among constants, the more frequent a ranks below b")
  }

  test("UnaryFirst puts unary symbols at the top of the precedence") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 2); val a = const("a"); val aS = fn("a", 0)
    Precedence.assign(sig, bank, Seq(clause(pos(mkEq(app(f, app(g, a, a)), a)))), PrecedenceScheme.UnaryFirst)
    assert(precOf(f) > precOf(g) && precOf(f) > precOf(aS), "the unary f must be precedence-maximal")
  }

  // ── A/B: the scheme must not change the verdict (only the search) ────────────────────────────────

  test("every scheme still refutes the UEQ problem f(a)=a, ¬f(f(a))=a (verdict is scheme-invariant)") {
    for scheme <- PrecedenceScheme.values do
      val fx = new Fix; import fx.*
      val f = fn("f", 1); val a = const("a")
      val cs = Seq(clause(pos(mkEq(app(f, a), a))), clause(neg(mkEq(app(f, app(f, a)), a))))
      Precedence.assign(sig, bank, cs, scheme)
      new Discount(bank, trail).saturate(cs, maxGiven = 1000) match
        case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
        case other => fail(s"$scheme: expected Refutation, got $other")
  }

  test("a satisfiable set still saturates under frequency precedence (no spurious refutation)") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val P = pred("P", 1)
    val cs = Seq(clause(pos(mkEq(a, b))), clause(pos(app(P, a))))
    Precedence.assign(sig, bank, cs, PrecedenceScheme.InvFrequency)
    assert(new Discount(bank, trail).saturate(cs, maxGiven = 1000) == Discount.Result.Saturated)
  }
