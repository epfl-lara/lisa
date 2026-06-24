package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Tests for the DISCOUNT saturation loop ([[Discount]]). */
class DiscountTest extends AnyFunSuite:

  class Fix:
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)

    def pred(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = true)
    def fn(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = false)
    def const(name: String): Term = bank.mkConst(fn(name, 0))
    def prop(name: String): Term = bank.mkConst(pred(name, 0)) // a 0-ary (propositional) atom
    def app(f: Symbol, args: Term*): Term = bank.mkApp(f, args.toArray)
    def v(n: Int): Term = bank.mkVar(Core.Variable(n))
    def pos(atom: Term): Literal = bank.mkLiteral(atom, true)
    def neg(atom: Term): Literal = bank.mkLiteral(atom, false)
    def clause(lits: Literal*): Clause = bank.mkClause(lits.toArray)
    def discount: Discount = new Discount(bank, trail)

  test("propositional P and ¬P refute") {
    val fx = new Fix; import fx.*
    val p = prop("P")
    val r = discount.saturate(Seq(clause(pos(p)), clause(neg(p))))
    assert(r.isInstanceOf[Discount.Result.Refutation])
  }

  test("propositional chain refutes") {
    val fx = new Fix; import fx.*
    val p = prop("P"); val q = prop("Q"); val rr = prop("R")
    val cs = Seq(
      clause(neg(p), pos(q)), //  ¬P ∨ Q
      clause(neg(q), pos(rr)), // ¬Q ∨ R
      clause(pos(p)), //          P
      clause(neg(rr)) //          ¬R
    )
    assert(discount.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  test("first-order resolution with unification refutes") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(q, x))), // ¬P(x) ∨ Q(x)
      clause(pos(app(p, a))), //                 P(a)
      clause(neg(app(q, a))) //                  ¬Q(a)
    )
    assert(discount.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  test("refutation that requires factoring") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val b = const("b")
    val x = v(0); val y = v(1)
    val cs = Seq(
      clause(pos(app(p, x)), pos(app(p, y))), //  P(x) ∨ P(y)
      clause(neg(app(p, a)), neg(app(p, b))) //  ¬P(a) ∨ ¬P(b)
    )
    assert(discount.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  test("a satisfiable set saturates") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val r = discount.saturate(Seq(clause(pos(app(p, a))), clause(pos(app(q, b)))))
    assert(r == Discount.Result.Saturated)
  }

  test("non-terminating generation hits the given-clause budget") {
    val fx = new Fix; import fx.*
    bank.selector = FirstNegativeSelector // resolve on the negative literal so the rule keeps firing
    val p = pred("P", 1); val f = fn("f", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(p, app(f, x)))), // ¬P(x) ∨ P(f(x)) -- generates P(f^n(a)) forever
      clause(pos(app(p, a))) //                          P(a)
    )
    assert(discount.saturate(cs, maxGiven = 5) == Discount.Result.Unknown)
  }

  test("complete selector (Vampire's default 10) drives a first-order refutation") {
    val fx = new Fix; import fx.*
    bank.selector = new CompleteBestLiteralSelector(new KBO(bank))
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(q, x))), // ¬P(x) ∨ Q(x)
      clause(pos(app(p, a))), //                 P(a)
      clause(neg(app(q, a))) //                  ¬Q(a)
    )
    assert(discount.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  test("complete selector refutes a factoring problem (selects all maximal positives)") {
    val fx = new Fix; import fx.*
    bank.selector = new CompleteBestLiteralSelector(new KBO(bank))
    val p = pred("P", 1); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
    val cs = Seq(
      clause(pos(app(p, x)), pos(app(p, y))), //  P(x) ∨ P(y) -- both maximal, both selected
      clause(neg(app(p, a)), neg(app(p, b))) //  ¬P(a) ∨ ¬P(b)
    )
    assert(discount.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  test("the refutation's empty clause traces back to the input clauses") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(q, x))),
      clause(pos(app(p, a))),
      clause(neg(app(q, a)))
    )
    discount.saturate(cs) match
      case Discount.Result.Refutation(empty) =>
        def inputLeaves(c: Clause): Int = c.justification match
          case Justification.Input => 1
          case Justification.Resolution(l, _, r, _) => inputLeaves(l) + inputLeaves(r)
          case Justification.Factoring(par, _, _) => inputLeaves(par)
          case Justification.Canonicalization(par) => inputLeaves(par)
        assert(empty.isEmpty)
        assert(inputLeaves(empty) >= 2) // derived from at least two input clauses
      case other => fail(s"expected Refutation, got $other")
  }
