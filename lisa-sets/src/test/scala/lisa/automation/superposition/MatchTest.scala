package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core._

/**
 * Tests for one-sided (first-order) matching ([[Core.Trail.matchTerm]] / [[Core.Trail.matchLiteral]]).
 *  Convention: pattern = scope 0 (its variables bind), target = scope 1 (rigid).
 */
class MatchTest extends AnyFunSuite:

  class Fix extends TermFixture:

    /**
     * Match `pat` (pattern) onto `tgt` (target), bracketed so the trail is left clean.
     */
    def m(pat: Term, tgt: Term): Boolean =
      val s = trail.save()
      val r = trail.matchTerm(pat, 0, tgt, 1)
      trail.restore(s)
      r

  test("a pattern variable matches any target term (and binds to it)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val f = fn("f", 1)
    assert(m(app(p, v(0)), app(p, a))) //        P(x) ↦ P(a)
    assert(m(app(p, v(0)), app(p, app(f, a)))) // P(x) ↦ P(f(a))
  }

  test("a non-variable pattern does not match a rigid target variable") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val f = fn("f", 1)
    assert(!m(app(p, a), app(p, v(0)))) //          P(a)    onto P(y): target var is rigid
    assert(!m(app(p, app(f, v(0))), app(p, v(1)))) // P(f(x)) onto P(y): compound vs rigid var
  }

  test("a pattern variable may match a rigid target variable") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1)
    // pattern x (scope 0) onto target y (scope 1): distinct by scope, so x binds to the rigid y
    assert(m(app(p, v(0)), app(p, v(1))))
    assert(m(app(p, v(0)), app(p, v(0)))) // same number, different scope -- still fine
  }

  test("matching is consistent within a single call (a variable binds once)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 2); val a = const("a"); val b = const("b")
    assert(m(app(p, v(0), v(0)), app(p, a, a))) //  P(x,x) ↦ P(a,a)
    assert(!m(app(p, v(0), v(0)), app(p, a, b))) // P(x,x) ✗ P(a,b)
  }

  test("nested function terms match structurally") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val f = fn("f", 1); val g = fn("g", 1); val a = const("a")
    assert(m(app(p, app(f, v(0))), app(p, app(f, a)))) //  P(f(x)) ↦ P(f(a))
    assert(!m(app(p, app(f, v(0))), app(p, app(g, a)))) // P(f(x)) ✗ P(g(a)): head mismatch
  }

  test("different head symbols or arities do not match") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    assert(!m(app(p, a), app(q, a)))
  }

  test("matching extends one shared substitution across literals (the subsumption use)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {P(x), Q(x)} matched against {P(a), Q(a)} with one σ (x ↦ a): both succeed under a shared trail
    locally {
      val s = trail.save()
      assert(trail.matchLiteral(pos(app(p, v(0))), 0, pos(app(p, a)), 1))
      assert(trail.matchLiteral(pos(app(q, v(0))), 0, pos(app(q, a)), 1))
      trail.restore(s)
    }
    // but against {P(a), Q(b)} the shared x cannot be both a and b: the second match fails
    locally {
      val s = trail.save()
      assert(trail.matchLiteral(pos(app(p, v(0))), 0, pos(app(p, a)), 1))
      assert(!trail.matchLiteral(pos(app(q, v(0))), 0, pos(app(q, b)), 1))
      trail.restore(s)
    }
  }

  test("matchLiteral requires equal polarity") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    val s = trail.save()
    assert(!trail.matchLiteral(pos(app(p, v(0))), 0, neg(app(p, a)), 1)) // + onto - : no
    assert(trail.matchLiteral(neg(app(p, v(0))), 0, neg(app(p, a)), 1)) //  - onto - : yes
    trail.restore(s)
  }

  test("the trail is left clean after a (bracketed) match attempt") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    val before = trail.save()
    assert(m(app(p, v(0)), app(p, a)))
    assert(trail.save() == before) // m brackets with save/restore: nothing leaks
    // a failing match also leaves the trail clean for the caller (restore on both paths)
    val s = trail.save()
    assert(!trail.matchTerm(app(p, a), 0, app(p, v(0)), 1))
    trail.restore(s)
    assert(trail.save() == before)
  }

  test("matching handles wide terms (worklist grows past its initial size)") {
    val fx = new Fix; import fx.*
    val k = 50 // forces matchPat/matchTgt to grow when all argument pairs are pushed at once
    val q = sig.intern("q", k, isPredicate = true)
    val a = const("a")
    val vars: Array[Term] = Array.tabulate(k)(i => v(i)) // q(x0, ..., x49)
    val consts: Array[Term] = Array.fill(k)(a) //          q(a, ..., a)
    assert(m(bank.mkApp(q, vars), bank.mkApp(q, consts))) // every xi ↦ a
  }

  // --- edge cases -----------------------------------------------------------------------------

  test("matching is one-sided: a pattern variable matches a target that contains it (no occurs check)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1)
    // x (pattern, scope 0) onto f(x) (target, scope 1): unification would fail the occurs check, but
    // the target's x is a different scope and rigid, so matching simply binds x ↦ f(y).
    assert(m(v(0), app(f, v(0))))
  }

  test("a variable bound to a compound is re-checked structurally (offset equality on compounds)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 2); val f = fn("f", 1); val a = const("a"); val b = const("b")
    assert(m(app(p, v(0), v(0)), app(p, app(f, a), app(f, a)))) //  x ↦ f(a), consistent on both
    assert(!m(app(p, v(0), v(0)), app(p, app(f, a), app(f, b)))) // f(a) ≠ f(b): the second use clashes
  }

  test("a repeated pattern variable against rigid target variables") {
    val fx = new Fix; import fx.*
    val p = pred("P", 2)
    assert(m(app(p, v(0), v(0)), app(p, v(1), v(1)))) //  x ↦ y, used twice consistently (y is rigid)
    assert(!m(app(p, v(0), v(0)), app(p, v(1), v(2)))) // x cannot be both y and z
  }

  test("distinct pattern variables may match the same target term (matching is not injective)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 2); val a = const("a")
    // term-level matching imposes no injectivity (that is a clause-level subsumption concern)
    assert(m(app(p, v(0), v(1)), app(p, a, a))) // x ↦ a, y ↦ a
  }

  test("nullary (propositional) atoms match by symbol identity") {
    val fx = new Fix; import fx.*
    val pp = pred("P", 0); val qq = pred("Q", 0)
    assert(m(bank.mkConst(pp), bank.mkConst(pp)))
    assert(!m(bank.mkConst(pp), bank.mkConst(qq)))
  }

  test("term-level matching: a top-level variable, identical and distinct ground terms") {
    val fx = new Fix; import fx.*
    val a = const("a"); val b = const("b")
    assert(m(v(0), a)) // x ↦ a at the very top level
    assert(m(a, a)) //    identical ground terms match (no binding)
    assert(!m(a, b)) //   distinct constants do not
  }

  test("a mismatch deep inside nested structure fails") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val f = fn("f", 2); val g = fn("g", 1)
    val a = const("a"); val b = const("b"); val c = const("c")
    assert(m(app(p, app(f, app(g, v(0)), a)), app(p, app(f, app(g, b), a)))) //  x ↦ b deep inside
    assert(!m(app(p, app(f, app(g, v(0)), a)), app(p, app(f, app(g, b), c)))) // a ≠ c in the sibling arg
  }

  test("a failed match does not leak bindings into an independent later match") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val b = const("b")
    // each bracketed call is self-contained: a genuine failure must not affect the next attempt
    assert(!m(app(p, b), app(p, a))) //  P(b) ✗ P(a)
    assert(m(app(p, v(0)), app(p, a))) // x still free afterwards: P(x) ↦ P(a)
  }
