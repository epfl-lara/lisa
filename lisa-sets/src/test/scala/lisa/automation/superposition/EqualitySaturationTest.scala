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

  test("the master equality=false switch skips every equality inference (UEQ not refuted)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val axiom = clause(pos(mkEq(app(f, a), a)))
    val goal = clause(neg(mkEq(app(f, app(f, a)), a)))
    // superposition, equality resolution, equality factoring AND demodulation are all off ⇒ nothing derivable
    val d = new Discount(bank, trail, equality = false)
    assert(d.saturate(Seq(axiom, goal), maxGiven = 1000) == Discount.Result.Saturated)
  }

  test("equality=false disables equality resolution too (a ≠ a is not closed)") {
    val fx = new Fix; import fx.*
    val a = const("a")
    // contrast with "equality resolution alone refutes a ≠ a": that inference is gated by the master flag
    assert(new Discount(bank, trail, equality = false).saturate(Seq(clause(neg(mkEq(a, a))))) == Discount.Result.Saturated)
  }

  test("equality=false leaves ordinary resolution intact (a purely propositional refutation still closes)") {
    val fx = new Fix; import fx.*
    val P = pred("P", 0)
    val cs = Seq(clause(pos(app(P))), clause(neg(app(P)))) // {P}, {¬P}
    new Discount(bank, trail, equality = false).saturate(cs) match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("fingerprint-indexed superposition and the linear scan reach the same verdict (A/B equivalence)") {
    // The index is a candidate filter confirmed by real unification, so both paths must generate the same
    // inference set and hence the same refuted/saturated verdict (clause ids differ, the outcome doesn't).
    def cat(r: Discount.Result): String = r match
      case _: Discount.Result.Refutation => "refuted"
      case Discount.Result.Saturated     => "saturated"
      case Discount.Result.Unknown       => "unknown"
    def verdict(indexed: Boolean, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, fingerprintIndexing = indexed).saturate(cs, maxGiven = 5000))

    val builders: Seq[(String, Fix => Seq[Clause])] = Seq(
      "ueq f(a)=a ⊢ f(f(a))=a" -> { fx => import fx.*; val f = fn("f", 1); val a = const("a")
        Seq(clause(pos(mkEq(app(f, a), a))), clause(neg(mkEq(app(f, app(f, a)), a)))) },
      "chain b=a,c=b,d=c ⊢ d=a" -> { fx => import fx.*
        val a = const("a"); val b = const("b"); val c = const("c"); val d = const("d")
        Seq(clause(pos(mkEq(b, a))), clause(pos(mkEq(c, b))), clause(pos(mkEq(d, c))), clause(neg(mkEq(d, a)))) },
      "two axioms f(x)=g(x), g(a)=b ⊢ f(a)=b" -> { fx => import fx.*
        val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val b = const("b"); val x = v(0)
        Seq(clause(pos(mkEq(app(f, x), app(g, x)))), clause(pos(mkEq(app(g, a), b))), clause(neg(mkEq(app(f, a), b)))) },
      "superpose into a predicate: f(a)=b, P(f(a)), ¬P(b)" -> { fx => import fx.*
        val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
        Seq(clause(pos(mkEq(app(f, a), b))), clause(pos(app(P, app(f, a)))), clause(neg(app(P, b)))) },
      "satisfiable a=b, P(a)" -> { fx => import fx.*
        val a = const("a"); val b = const("b"); val P = pred("P", 1)
        Seq(clause(pos(mkEq(a, b))), clause(pos(app(P, a)))) }
    )
    for (name, b) <- builders do
      assert(verdict(indexed = true, b) == verdict(indexed = false, b), s"index vs scan verdict differ on: $name")
  }

  test("discrimination-tree forward demodulation and the linear scan reach the same verdict (A/B equivalence)") {
    // The perfect discrimination tree returns exactly the matching demodulators (σ on the trail), so the indexed
    // and scanned forward-demodulation paths must reach the same verdict (clause ids/trajectory differ, not the outcome).
    def cat(r: Discount.Result): String = r match
      case _: Discount.Result.Refutation => "refuted"
      case Discount.Result.Saturated     => "saturated"
      case Discount.Result.Unknown       => "unknown"
    def verdict(indexed: Boolean, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, demodulationIndexing = indexed).saturate(cs, maxGiven = 5000))

    val builders: Seq[(String, Fix => Seq[Clause])] = Seq(
      "ueq f(a)=a ⊢ f(f(a))=a (nested rewrite)" -> { fx => import fx.*; val f = fn("f", 1); val a = const("a")
        Seq(clause(pos(mkEq(app(f, a), a))), clause(neg(mkEq(app(f, app(f, a)), a)))) },
      "chain b=a,c=b,d=c ⊢ d=a (demodulation chain)" -> { fx => import fx.*
        val a = const("a"); val b = const("b"); val c = const("c"); val d = const("d")
        Seq(clause(pos(mkEq(b, a))), clause(pos(mkEq(c, b))), clause(pos(mkEq(d, c))), clause(neg(mkEq(d, a)))) },
      "rewrite with a variable rule f(x)=g(x), g(a)=b ⊢ f(a)=b" -> { fx => import fx.*
        val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val b = const("b"); val x = v(0)
        Seq(clause(pos(mkEq(app(f, x), app(g, x)))), clause(pos(mkEq(app(g, a), b))), clause(neg(mkEq(app(f, a), b)))) },
      "demodulate into a predicate: f(a)=b, P(f(a)), ¬P(b)" -> { fx => import fx.*
        val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
        Seq(clause(pos(mkEq(app(f, a), b))), clause(pos(app(P, app(f, a)))), clause(neg(app(P, b)))) },
      "deep nesting g(g(a))=a ⊢ g(g(g(g(a))))=a" -> { fx => import fx.*
        val g = fn("g", 1); val a = const("a")
        def gg(t: Term, n: Int): Term = if n == 0 then t else gg(app(g, t), n - 1)
        Seq(clause(pos(mkEq(gg(a, 2), a))), clause(neg(mkEq(gg(a, 4), a)))) },
      "backward: P(f(a)), Q(f(a)) collapsed by a later f(a)=a, ¬P(a)" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val f = fn("f", 1); val a = const("a")
        Seq(clause(pos(app(P, app(f, a)))), clause(pos(app(Q, app(f, a)))),
            clause(pos(mkEq(app(f, a), a))), clause(neg(app(P, a)))) },
      "satisfiable a=b, P(a)" -> { fx => import fx.*
        val a = const("a"); val b = const("b"); val P = pred("P", 1)
        Seq(clause(pos(mkEq(a, b))), clause(pos(app(P, a)))) }
    )
    for (name, b) <- builders do
      assert(verdict(indexed = true, b) == verdict(indexed = false, b), s"demod index vs scan verdict differ on: $name")
  }
