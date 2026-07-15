package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Phase-4 Step 4: the DISCOUNT loop with the equality inferences (superposition, equality resolution,
 *  equality factoring) and the `s = s` tautology drop wired in. */
class EqualitySaturationTest extends AnyFunSuite:

  class Fix:
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)
    bank.selector = new CompleteBestLiteralSelector(bank.order)

    def pred(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = true)
    def fn(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = false)
    def const(name: String): Term = bank.mkConst(fn(name, 0))
    def app(f: Symbol, args: Term*): Term = bank.mkApp(f, args.toArray)
    def v(n: Int): Term = bank.mkVar(Core.Variable(n))
    def mkEq(s: Term, t: Term): Term = bank.mkApp(EqualitySymbol, Array(s, t))
    def pos(atom: Term): Literal = bank.mkLiteral(atom, true)
    def neg(atom: Term): Literal = bank.mkLiteral(atom, false)
    def clause(lits: Literal*): Clause = bank.mkClause(lits.toArray)

  test("UEQ refutation: f(a)=a, ¬(f(f(a))=a) reduces to □ via superposition + equality resolution") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val axiom = clause(pos(mkEq(app(f, a), a))) //          f(a) = a
    val goal = clause(neg(mkEq(app(f, app(f, a)), a))) //   f(f(a)) ≠ a
    new Discount(bank, trail).saturate(Seq(axiom, goal)) match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("equality resolution alone refutes a ≠ a") {
    val fx = new Fix; import fx.*
    val a = const("a")
    new Discount(bank, trail).saturate(Seq(clause(neg(mkEq(a, a))))) match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("a positive trivial equality s = s is dropped as a tautology (no refutation from it)") {
    val fx = new Fix; import fx.*
    val a = const("a")
    // {a = a} is a tautology ⇒ discarded ⇒ passive empties ⇒ Saturated (not a refutation)
    assert(new Discount(bank, trail).saturate(Seq(clause(pos(mkEq(a, a))))) == Discount.Result.Saturated)
  }

  test("a satisfiable equality set saturates") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val P = pred("P", 1)
    val cs = Seq(clause(pos(mkEq(a, b))), clause(pos(app(P, a)))) // a = b, P(a)
    assert(new Discount(bank, trail).saturate(cs, maxGiven = 1000) == Discount.Result.Saturated)
  }

  test("a chain of unit equalities refutes an inequality of its endpoints (demodulation/superposition chaining)") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val c = const("c"); val d = const("d") // a ≺ b ≺ c ≺ d
    // b = a, c = b, d = c, d ≠ a  ⇒  d normalises to a, so d ≠ a closes to □
    val cs = Seq(clause(pos(mkEq(b, a))), clause(pos(mkEq(c, b))), clause(pos(mkEq(d, c))), clause(neg(mkEq(d, a))))
    new Discount(bank, trail).saturate(cs) match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("with all equality rewriting off the UEQ problem is not refuted (isolates the rewriting inferences)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val axiom = clause(pos(mkEq(app(f, a), a)))
    val goal = clause(neg(mkEq(app(f, app(f, a)), a)))
    // both superposition and demodulation bridge f(f(a)) and a; with both off, nothing does ⇒ Saturated
    val d = new Discount(bank, trail, superposition = false, forwardDemodulation = false, backwardDemodulation = false)
    assert(d.saturate(Seq(axiom, goal), maxGiven = 1000) == Discount.Result.Saturated)
  }
