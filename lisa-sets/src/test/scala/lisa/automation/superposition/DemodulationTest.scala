package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Tests for Phase-4 Step 3 demodulation ([[Demodulation]]). */
class DemodulationTest extends AnyFunSuite:

  class Fix:
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)
    val order: Order = bank.order

    def pred(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = true)
    def fn(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = false)
    def const(name: String): Term = bank.mkConst(fn(name, 0))
    def app(f: Symbol, args: Term*): Term = bank.mkApp(f, args.toArray)
    def v(n: Int): Term = bank.mkVar(Core.Variable(n))
    def mkEq(s: Term, t: Term): Term = bank.mkApp(EqualitySymbol, Array(s, t))
    def pos(atom: Term): Literal = bank.mkLiteral(atom, true)
    def neg(atom: Term): Literal = bank.mkLiteral(atom, false)
    def clause(lits: Literal*): Clause = bank.mkClause(lits.toArray)

  // --- forward -----------------------------------------------------------------------------------

  test("forward demodulation normal-forms a clause by an oriented ground equation") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a")
    val rule = clause(pos(mkEq(app(f, a), a))) //  f(a) = a
    val c = clause(pos(app(P, app(f, app(f, a))))) // P(f(f(a)))
    val r = Demodulation.forwardDemodulate(bank, trail, order, c, List(rule))
    assert(r.literals.toSet == Set(pos(app(P, a)))) // f(f(a)) → f(a) → a
    r.justification match
      case Justification.Demodulation(_, _, _, ru, _) => assert(ru == rule)
      case other => fail(s"expected Demodulation, got $other")
  }

  test("forward demodulation applies an oriented rule with variables (matching)") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val g = fn("g", 1); val b = const("b"); val x = v(0)
    val rule = clause(pos(mkEq(app(g, x), x))) // g(x) = x
    val c = clause(pos(app(P, app(g, b)))) //     P(g(b))
    val r = Demodulation.forwardDemodulate(bank, trail, order, c, List(rule))
    assert(r.literals.toSet == Set(pos(app(P, b)))) // x ↦ b, g(b) → b
  }

  test("forward demodulation leaves a clause unchanged when no rule applies") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val rule = clause(pos(mkEq(app(f, a), a))) // f(a) = a
    val c = clause(pos(app(P, b))) //            P(b)
    val r = Demodulation.forwardDemodulate(bank, trail, order, c, List(rule))
    assert(r.id == c.id) // identity ⇒ untouched
  }

  // --- orientation-after-matching guard ----------------------------------------------------------

  test("an unoriented rule rewrites only the instance that is oriented after matching") {
    val fx = new Fix; import fx.*
    // a interned before b ⇒ a ≺ b, so f(b,a) ≻ f(a,b)
    val P = pred("P", 1); val f = fn("f", 2); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
    val comm = clause(pos(mkEq(app(f, x, y), app(f, y, x)))) // f(x,y) = f(y,x)  (unoriented)
    // f(a,b) is already minimal ⇒ not rewritten (both directions fail the post-match ≻ check)
    val cMin = clause(pos(app(P, app(f, a, b))))
    assert(Demodulation.forwardDemodulate(bank, trail, order, cMin, List(comm)).id == cMin.id)
    // f(b,a) ≻ f(a,b) ⇒ rewritten down to f(a,b)
    val cMax = clause(pos(app(P, app(f, b, a))))
    val r = Demodulation.forwardDemodulate(bank, trail, order, cMax, List(comm))
    assert(r.literals.toSet == Set(pos(app(P, app(f, a, b)))))
  }

  // --- backward ----------------------------------------------------------------------------------

  test("backward demodulation rewrites an active clause with a new unit equation") {
    val fx = new Fix; import fx.*
    val Q = pred("Q", 1); val g = fn("g", 1); val b = const("b"); val x = v(0)
    val active = clause(pos(app(Q, app(g, b)))) // Q(g(b))  (already processed)
    val newEq = clause(pos(mkEq(app(g, x), x))) // g(x) = x  (just arrived)
    val pairs = Demodulation.backwardDemodulate(bank, trail, order, newEq, List(active))
    assert(pairs.length == 1)
    val (removed, replacement) = pairs.head
    assert(removed.id == active.id)
    assert(replacement.literals.toSet == Set(pos(app(Q, b))))
  }

  // --- redundancy gate (encompassment): simplify vs. skip ----------------------------------------

  test("the redundancy gate skips a renaming matcher on the big side of a positive unit equality") {
    val fx = new Fix; import fx.*
    // c interned before h ⇒ h ≻ c, so the rewrite is NOT a rewrite-the-bigger-side-down case
    val g = fn("g", 1); val c0 = const("c"); val h = const("h"); val x = v(0); val y = v(1)
    val rule = clause(pos(mkEq(app(g, y), h))) // g(y) = h
    val target = clause(pos(mkEq(app(g, x), c0))) // g(x) = c   (g(x) is the maximal side)
    // matching g(y) onto g(x) is a renaming (y ↦ x) ⇒ not redundant ⇒ skip
    val r = Demodulation.forwardDemodulate(bank, trail, order, target, List(rule))
    assert(r.id == target.id)
  }

  test("the redundancy gate simplifies with a proper (non-renaming) instance on the big side") {
    val fx = new Fix; import fx.*
    val g = fn("g", 1); val f = fn("f", 1); val c0 = const("c"); val h = const("h"); val b = const("b"); val y = v(1)
    val rule = clause(pos(mkEq(app(g, y), h))) //      g(y) = h
    val target = clause(pos(mkEq(app(g, app(f, b)), c0))) // g(f(b)) = c
    // matching g(y) onto g(f(b)) binds y ↦ f(b): a proper instance ⇒ redundant ⇒ simplify to h = c
    val r = Demodulation.forwardDemodulate(bank, trail, order, target, List(rule))
    assert(r.id != target.id)
    assert(r.literals.toSet == Set(pos(mkEq(h, c0))))
  }
