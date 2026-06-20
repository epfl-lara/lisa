package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Tests for the generating inference rules ([[Inference.resolve]], [[Inference.factor]]). */
class InferenceTest extends AnyFunSuite:

  class Fix:
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)

    def pred(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = true)
    def fn(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = false)
    def const(name: String): Term = bank.mkConst(fn(name, 0))
    def app(f: Symbol, args: Term*): Term = bank.mkApp(f, args.toArray)
    def v(n: Int): Term = bank.mkVar(Core.Variable(n))
    def pos(atom: Term): Literal = bank.mkLiteral(atom, true)
    def neg(atom: Term): Literal = bank.mkLiteral(atom, false)
    def clause(lits: Literal*): Clause = bank.mkClause(lits.toArray)

  test("resolution unifies complementary literals and applies the mgu") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    val x = v(0)
    val c1 = clause(neg(app(p, x)), pos(app(q, x))) // ¬P(x) ∨ Q(x)
    val c2 = clause(pos(app(p, a))) //                P(a)
    val r = Inference.resolve(bank, trail, c1, 0, c2, 0)
    assert(r.isDefined)
    val res = r.get
    assert(res.size == 1)
    assert(res.literals(0) == pos(app(q, a))) // Q(a)
    res.justification match
      case Justification.Resolution(l, li, rr, ri) => assert(l == c1 && li == 0 && rr == c2 && ri == 0)
      case other => fail(s"expected Resolution, got $other")
    assert(res.age == 1)
  }

  test("resolution can produce the empty clause") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    val c1 = clause(neg(app(p, a))) // ¬P(a)
    val c2 = clause(pos(app(p, a))) //  P(a)
    val r = Inference.resolve(bank, trail, c1, 0, c2, 0)
    assert(r.isDefined && r.get.isEmpty) // □
  }

  test("resolution keeps the parents' variables apart via scopes") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val f = fn("f", 1)
    val x = v(0) // var 0 in c1
    val y = v(0) // var 0 in c2 -- same number, different clause
    val c1 = clause(neg(app(p, x)), pos(app(q, x))) // ¬P(x) ∨ Q(x)
    val c2 = clause(pos(app(p, app(f, y)))) //          P(f(y))
    val res = Inference.resolve(bank, trail, c1, 0, c2, 0).get
    // x ↦ f(y); Q(x) ↦ Q(f(y)); the surviving variable is renamed to a fresh 0
    assert(res.size == 1)
    assert(res.literals(0) == pos(app(q, app(f, v(0)))))
  }

  test("resolution fails on non-complementary or non-unifiable literals") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val b = const("b")
    val c1 = clause(pos(app(p, a)))
    val c2 = clause(pos(app(p, a)))
    assert(Inference.resolve(bank, trail, c1, 0, c2, 0).isEmpty) // same polarity
    val c3 = clause(neg(app(p, b)))
    assert(Inference.resolve(bank, trail, c1, 0, c3, 0).isEmpty) // P(a) vs P(b) don't unify
  }

  test("factoring merges two same-polarity literals") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    val c = clause(pos(app(p, x)), pos(app(p, a))) // P(x) ∨ P(a)
    val res = Inference.factor(bank, trail, c, 0, 1).get
    assert(res.size == 1)
    assert(res.literals(0) == pos(app(p, a))) // x ↦ a, literal 1 dropped
    res.justification match
      case Justification.Factoring(par, i, j) => assert(par == c && i == 0 && j == 1)
      case other => fail(s"expected Factoring, got $other")
    assert(res.age == 1)
  }

  test("factoring fails on different polarity or non-unifiable literals") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val b = const("b")
    val c1 = clause(pos(app(p, a)), neg(app(p, a))) // different polarity
    assert(Inference.factor(bank, trail, c1, 0, 1).isEmpty)
    val c2 = clause(pos(app(p, a)), pos(app(p, b))) // a vs b don't unify
    assert(Inference.factor(bank, trail, c2, 0, 1).isEmpty)
  }

  test("default selector prefers a negative equality literal (key 1)") {
    val fx = new Fix; import fx.*
    val eqSym = sig.intern("=", 2, isPredicate = true) // code 0 by convention (interned first)
    assert(eqSym.code == 0)
    val p = pred("P", 1); val f = fn("f", 1)
    val a = const("a"); val b = const("b"); val c = const("c")
    val heavyPos = pos(app(p, app(f, app(f, a)))) // P(f(f(a))), weight 4
    val negEq = neg(app(eqSym, b, c)) //              ¬(b = c),    weight 3
    val cl = clause(heavyPos, negEq)
    assert(cl.select(bank).toSeq == Seq(1)) // negative equality wins despite being lighter
  }

  test("default selector prefers the heavier literal when no equality and same sign (key 2)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val f = fn("f", 1); val a = const("a")
    val cl = clause(neg(app(p, a)), neg(app(q, app(f, a)))) // ¬P(a) [w2], ¬Q(f(a)) [w3]
    assert(cl.select(bank).toSeq == Seq(1)) // the heavier negative literal
  }

  test("default selector prefers a negative literal when sizes tie (key 3)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    val cl = clause(pos(app(p, a)), neg(app(q, a))) // P(a) [w2, +], ¬Q(a) [w2, -]
    assert(cl.select(bank).toSeq == Seq(1)) // negative preferred
  }

  test("default selection is total and deterministic on otherwise-tied literals (key 4)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val cl1 = clause(pos(app(p, a)), pos(app(q, b))) // tie on keys 1-3, distinct atoms
    assert(cl1.select(bank).length == 1)
    val cl2 = clause(pos(app(p, a)), pos(app(q, b)))
    assert(cl1.select(bank).toSeq == cl2.select(bank).toSeq) // deterministic
  }

  test("selection is computed once and cached (idempotent)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    val cl = clause(neg(app(p, a)))
    assert(cl.selected == null) // not computed until activation
    val s = cl.select(bank)
    assert(cl.selected eq s) // stored; subsequent select returns the same array
    assert((cl.select(bank) eq s))
  }

  test("a pluggable selector can select many literals (AllNegative)") {
    val fx = new Fix; import fx.*
    bank.selector = AllNegativeSelector
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1); val a = const("a")
    val c = clause(neg(app(p, a)), pos(app(q, a)), neg(app(r, a))) // negatives at 0 and 2
    assert(c.select(bank).toSeq == Seq(0, 2))
    val allPos = clause(pos(app(p, a)), pos(app(q, a))) // no negatives -> first
    assert(allPos.select(bank).toSeq == Seq(0))
  }

  test("FirstNegativeSelector remains available as a pluggable strategy") {
    val fx = new Fix; import fx.*
    bank.selector = FirstNegativeSelector
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    val cl = clause(pos(app(p, a)), neg(app(q, a)))
    assert(cl.select(bank).toSeq == Seq(1)) // the first (here, only) negative literal
  }

  test("the trail is left clean after an inference") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    val c1 = clause(neg(app(p, x)))
    val c2 = clause(pos(app(p, a)))
    val before = trail.save()
    Inference.resolve(bank, trail, c1, 0, c2, 0)
    assert(trail.save() == before) // bindings restored, trail top unchanged
  }
