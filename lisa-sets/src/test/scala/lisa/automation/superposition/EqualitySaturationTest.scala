package lisa.automation.superposition

import lisa.automation.superposition.ordering._
import org.scalatest.funsuite.AnyFunSuite

import Core._

/**
 * The DISCOUNT loop with the equality inferences (superposition, equality resolution, equality factoring)
 *  and the `s = s` tautology drop wired in.
 */
class EqualitySaturationTest extends AnyFunSuite:

  // The bank's default selection is already the complete one, so `Fix` adds nothing to [[TermFixture]].
  class Fix extends TermFixture

  /**
   * The saturation verdict as a string, so a table of expected outcomes reads directly.
   */
  private def cat(r: Discount.Result): String = r match
    case _: Discount.Result.Refutation => "refuted"
    case Discount.Result.Saturated => "saturated"
    case Discount.Result.Unknown => "unknown"

  test("UEQ refutation: f(a)=a, ¬(f(f(a))=a) reduces to □ via superposition + equality resolution") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val axiom = clause(pos(mkEq(app(f, a), a))) //          f(a) = a
    val goal = clause(neg(mkEq(app(f, app(f, a)), a))) //   f(f(a)) ≠ a
    new Discount(bank, trail, Seq(axiom, goal)).saturate() match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("equality resolution alone refutes a ≠ a") {
    val fx = new Fix; import fx.*
    val a = const("a")
    new Discount(bank, trail, Seq(clause(neg(mkEq(a, a))))).saturate() match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("a positive trivial equality s = s is dropped as a tautology (no refutation from it)") {
    val fx = new Fix; import fx.*
    val a = const("a")
    // {a = a} is a tautology ⇒ discarded ⇒ passive empties ⇒ Saturated (not a refutation)
    assert(new Discount(bank, trail, Seq(clause(pos(mkEq(a, a))))).saturate() == Discount.Result.Saturated)
  }

  test("a satisfiable equality set saturates") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val P = pred("P", 1)
    val cs = Seq(clause(pos(mkEq(a, b))), clause(pos(app(P, a)))) // a = b, P(a)
    assert(new Discount(bank, trail, cs, SearchOptions(maxGiven = 1000)).saturate() == Discount.Result.Saturated)
  }

  test("a chain of unit equalities refutes an inequality of its endpoints (demodulation/superposition chaining)") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b"); val c = const("c"); val d = const("d") // a ≺ b ≺ c ≺ d
    // b = a, c = b, d = c, d ≠ a  ⇒  d normalises to a, so d ≠ a closes to □
    val cs = Seq(clause(pos(mkEq(b, a))), clause(pos(mkEq(c, b))), clause(pos(mkEq(d, c))), clause(neg(mkEq(d, a))))
    new Discount(bank, trail, cs).saturate() match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("with all equality rewriting off the UEQ problem is not refuted (isolates the rewriting inferences)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val axiom = clause(pos(mkEq(app(f, a), a)))
    val goal = clause(neg(mkEq(app(f, app(f, a)), a)))
    // both superposition and demodulation bridge f(f(a)) and a; with both off, nothing does ⇒ Saturated
    val d = new Discount(bank, trail, Seq(axiom, goal), SearchOptions(superposition = false, forwardDemodulation = false, backwardDemodulation = false, maxGiven = 1000))
    assert(d.saturate() == Discount.Result.Saturated)
  }

  test("the master equality=false switch skips every equality inference (UEQ not refuted)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val axiom = clause(pos(mkEq(app(f, a), a)))
    val goal = clause(neg(mkEq(app(f, app(f, a)), a)))
    // superposition, equality resolution, equality factoring AND demodulation are all off ⇒ nothing derivable
    val d = new Discount(bank, trail, Seq(axiom, goal), SearchOptions(equality = false, maxGiven = 1000))
    assert(d.saturate() == Discount.Result.Saturated)
  }

  test("equality=false disables equality resolution too (a ≠ a is not closed)") {
    val fx = new Fix; import fx.*
    val a = const("a")
    // contrast with "equality resolution alone refutes a ≠ a": that inference is gated by the master flag
    val cs = Seq(clause(neg(mkEq(a, a))))
    assert(new Discount(bank, trail, cs, SearchOptions(equality = false)).saturate() == Discount.Result.Saturated)
  }

  test("equality=false leaves ordinary resolution intact (a purely propositional refutation still closes)") {
    val fx = new Fix; import fx.*
    val P = pred("P", 0)
    val cs = Seq(clause(pos(app(P))), clause(neg(app(P)))) // {P}, {¬P}
    new Discount(bank, trail, cs, SearchOptions(equality = false)).saturate() match
      case Discount.Result.Refutation(empty) => assert(empty.isEmpty)
      case other => fail(s"expected Refutation, got $other")
  }

  test("indexed superposition reaches the expected verdict on each shape of equality problem") {
    // Was an A/B comparison against a linear-scan superposition arm, which no longer exists; the verdicts are
    // pinned instead, so the same clause sets still pin the behaviour of the surviving path. The fingerprint
    // indices only narrow the candidate set, and every candidate is confirmed by a real unification, so these
    // verdicts are the calculus's and not the index's.
    def verdict(build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, cs, SearchOptions(maxGiven = 5000)).saturate())

    val cases: Seq[(String, String, Fix => Seq[Clause])] = Seq(
      (
        "ueq f(a)=a ⊢ f(f(a))=a",
        "refuted",
        { fx =>
          import fx.*; val f = fn("f", 1); val a = const("a")
          Seq(clause(pos(mkEq(app(f, a), a))), clause(neg(mkEq(app(f, app(f, a)), a))))
        }
      ),
      (
        "chain b=a,c=b,d=c ⊢ d=a",
        "refuted",
        { fx =>
          import fx.*
          val a = const("a"); val b = const("b"); val c = const("c"); val d = const("d")
          Seq(clause(pos(mkEq(b, a))), clause(pos(mkEq(c, b))), clause(pos(mkEq(d, c))), clause(neg(mkEq(d, a))))
        }
      ),
      (
        "two axioms f(x)=g(x), g(a)=b ⊢ f(a)=b",
        "refuted",
        { fx =>
          import fx.*
          val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val b = const("b"); val x = v(0)
          Seq(clause(pos(mkEq(app(f, x), app(g, x)))), clause(pos(mkEq(app(g, a), b))), clause(neg(mkEq(app(f, a), b))))
        }
      ),
      (
        "superpose into a predicate: f(a)=b, P(f(a)), ¬P(b)",
        "refuted",
        { fx =>
          import fx.*
          val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
          Seq(clause(pos(mkEq(app(f, a), b))), clause(pos(app(P, app(f, a)))), clause(neg(app(P, b))))
        }
      ),
      (
        "satisfiable a=b, P(a)",
        "saturated",
        { fx =>
          import fx.*
          val a = const("a"); val b = const("b"); val P = pred("P", 1)
          Seq(clause(pos(mkEq(a, b))), clause(pos(app(P, a))))
        }
      )
    )
    for (name, expected, b) <- cases do assert(verdict(b) == expected, s"expected $expected on: $name")
  }

  test("discrimination-tree demodulation reaches the expected verdict on each shape of rewriting problem") {
    // Was an A/B comparison against a rule-list scan, which no longer exists; the verdicts are pinned instead.
    // The tree is *perfect*: reaching a leaf establishes the match outright, with σ already on the trail, so
    // there is nothing here that a scan could have found and it could not.
    def verdict(build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, cs, SearchOptions(maxGiven = 5000)).saturate())

    val cases: Seq[(String, String, Fix => Seq[Clause])] = Seq(
      (
        "ueq f(a)=a ⊢ f(f(a))=a (nested rewrite)",
        "refuted",
        { fx =>
          import fx.*; val f = fn("f", 1); val a = const("a")
          Seq(clause(pos(mkEq(app(f, a), a))), clause(neg(mkEq(app(f, app(f, a)), a))))
        }
      ),
      (
        "chain b=a,c=b,d=c ⊢ d=a (demodulation chain)",
        "refuted",
        { fx =>
          import fx.*
          val a = const("a"); val b = const("b"); val c = const("c"); val d = const("d")
          Seq(clause(pos(mkEq(b, a))), clause(pos(mkEq(c, b))), clause(pos(mkEq(d, c))), clause(neg(mkEq(d, a))))
        }
      ),
      (
        "rewrite with a variable rule f(x)=g(x), g(a)=b ⊢ f(a)=b",
        "refuted",
        { fx =>
          import fx.*
          val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val b = const("b"); val x = v(0)
          Seq(clause(pos(mkEq(app(f, x), app(g, x)))), clause(pos(mkEq(app(g, a), b))), clause(neg(mkEq(app(f, a), b))))
        }
      ),
      (
        "demodulate into a predicate: f(a)=b, P(f(a)), ¬P(b)",
        "refuted",
        { fx =>
          import fx.*
          val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
          Seq(clause(pos(mkEq(app(f, a), b))), clause(pos(app(P, app(f, a)))), clause(neg(app(P, b))))
        }
      ),
      (
        "deep nesting g(g(a))=a ⊢ g(g(g(g(a))))=a",
        "refuted",
        { fx =>
          import fx.*
          val g = fn("g", 1); val a = const("a")
          def gg(t: Term, n: Int): Term = if n == 0 then t else gg(app(g, t), n - 1)
          Seq(clause(pos(mkEq(gg(a, 2), a))), clause(neg(mkEq(gg(a, 4), a))))
        }
      ),
      (
        "backward: P(f(a)), Q(f(a)) collapsed by a later f(a)=a, ¬P(a)",
        "refuted",
        { fx =>
          import fx.*
          val P = pred("P", 1); val Q = pred("Q", 1); val f = fn("f", 1); val a = const("a")
          Seq(clause(pos(app(P, app(f, a)))), clause(pos(app(Q, app(f, a)))), clause(pos(mkEq(app(f, a), a))), clause(neg(app(P, a))))
        }
      ),
      (
        "satisfiable a=b, P(a)",
        "saturated",
        { fx =>
          import fx.*
          val a = const("a"); val b = const("b"); val P = pred("P", 1)
          Seq(clause(pos(mkEq(a, b))), clause(pos(app(P, a))))
        }
      )
    )
    for (name, expected, b) <- cases do assert(verdict(b) == expected, s"expected $expected on: $name")
  }
