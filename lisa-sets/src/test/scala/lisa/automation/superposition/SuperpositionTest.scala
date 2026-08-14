package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite
import it.unimi.dsi.fastutil.ints.IntArrayList

import Core.*

/** Tests for the Phase-4 generating equality inferences ([[Superposition]]). */
class SuperpositionTest extends AnyFunSuite:

  class Fix extends TermFixture:

    /** Locate + unify + [[Superposition.superpose]] and restore, which is what the loop and term index do around
     *  the build-only `superpose`. Tests drive superposition through this. */
    def superposeAt(from: Clause, iFrom: Int, fromSide: Int, into: Clause, iInto: Int, uPos: Array[Int]): Option[Clause] =
      val fromAtom = bank.atomOf(from.literals(iFrom))
      val intoAtom = bank.atomOf(into.literals(iInto))
      val l = bank.arg(fromAtom, fromSide)
      val u = Superposition.subtermAt(bank, intoAtom, uPos)
      val saved = trail.save()
      val res = if trail.unify(l, 0, u, 1) then Superposition.superpose(bank, trail, order, from, iFrom, fromSide, into, iInto, IntArrayList.wrap(uPos)) else None
      trail.restore(saved)
      res

  // --- superposition ------------------------------------------------------------------------------

  test("superposition rewrites a subterm of a (predicate) literal") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val from = clause(pos(mkEq(app(f, a), b))) //  f(a) = b   (f(a) ≻ b, oriented, side 0)
    val into = clause(pos(app(P, app(f, a)))) // P(f(a))
    // rewrite f(a) (position [0] of P(f(a))) by b ⇒ P(b)
    val r = superposeAt(from, 0, 0, into, 0, Array(0))
    assert(r.isDefined)
    assert(r.get.literals.toSet == Set(pos(app(P, b))))
    r.get.justification match
      case Justification.Superposition(fr, fl, fs, in, il, p) =>
        assert(fr == from && fl == 0 && fs == 0 && in == into && il == 0 && p.toList == List(0))
      case other => fail(s"expected Superposition, got $other")
  }

  test("superposition rewrites deep inside the maximal side of an equality") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val c = const("c")
    val from = clause(pos(mkEq(app(f, a), a))) //   f(a) = a
    val into = clause(pos(mkEq(app(g, app(f, a)), c))) // g(f(a)) = c   (g(f(a)) ≻ c)
    // f(a) sits at [0,0] (g(f(a))'s inner arg) ⇒ g(a) = c
    val r = superposeAt(from, 0, 0, into, 0, Array(0, 0))
    assert(r.isDefined)
    assert(r.get.literals.toSet == Set(pos(mkEq(app(g, a), c))))
  }

  test("superposition does not rewrite the strictly-smaller side of an equality into-literal") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a"); val b = const("b")
    val from = clause(pos(mkEq(a, b))) //          a = b   (a ≻ b since a interned first? make a ≻ b)
    // make a ≻ b explicit via precedence is automatic by intern order; ensure a is the bigger constant:
    sig.info(fn("a", 0)).precedence = 100
    val into = clause(pos(mkEq(app(f, b), a))) //  f(b) = a  (f(b) ≻ a). The `a` on the right is the SMALLER side.
    // trying to rewrite the smaller side `a` (position [1]) by b must be rejected
    val r = superposeAt(from, 0, 0, into, 0, Array(1))
    assert(r.isEmpty)
  }

  // --- equality resolution ------------------------------------------------------------------------

  test("equality resolution closes a unifiable disequality to the empty clause") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a"); val x = v(0)
    val c = clause(neg(mkEq(app(f, x), app(f, a)))) // f(x) ≠ f(a)
    val rs = Superposition.equalityResolution(bank, trail, order, c, Array(0))
    assert(rs.length == 1 && rs.head.isEmpty) // x ↦ a, literal dropped ⇒ □
    rs.head.justification match
      case Justification.EqualityResolution(p, i) => assert(p == c && i == 0)
      case other => fail(s"expected EqualityResolution, got $other")
  }

  test("equality resolution applies the mgu to the surviving literals") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val x = v(0)
    val c = clause(neg(mkEq(app(f, x), app(f, a))), pos(app(P, x))) // f(x) ≠ f(a) ∨ P(x)
    // eligibility (maximal/selected) is the loop's concern, supplied via the eligible set
    val rs = Superposition.equalityResolution(bank, trail, order, c, Array(0, 1))
    assert(rs.length == 1) // only the negative equality resolves; the positive predicate P(x) is skipped
    assert(rs.head.literals.toSet == Set(pos(app(P, a)))) // x ↦ a
  }

  test("equality resolution fails when the two sides do not unify") {
    val fx = new Fix; import fx.*
    val h = fn("h", 2); val a = const("a"); val b = const("b"); val x = v(0)
    val c = clause(neg(mkEq(app(h, x, x), app(h, a, b)))) // h(x,x) ≠ h(a,b): x ↦ a and x ↦ b clash
    assert(Superposition.equalityResolution(bank, trail, order, c, Array(0)).isEmpty)
  }

  // --- equality factoring -------------------------------------------------------------------------

  test("equality factoring drops the maximal equality, keeps the partner, adds the disequality") {
    val fx = new Fix; import fx.*
    val c0 = const("c"); val a = const("a"); val b = const("b"); val f = fn("f", 1); val x = v(0)
    val cl = clause(pos(mkEq(app(f, x), a)), pos(mkEq(app(f, b), c0))) // f(x)≈a ∨ f(b)≈c
    // σ = mgu(f(x), f(b)) = {x ↦ b}; the (i=0 dropped, j=1 kept) factor is a ≠ c ∨ f(b)≈c
    val factors = Superposition.equalityFactoring(bank, trail, order, cl, Array(0, 1))
    val expected = factors.find(_.literals.toSet == Set(neg(mkEq(a, c0)), pos(mkEq(app(f, b), c0))))
    assert(expected.isDefined) // among those enumerated over the ordered pairs / sides
    expected.get.justification match
      case Justification.EqualityFactoring(p, d, ds, k, ks) => assert(p == cl && d == 0 && ds == 0 && k == 1 && ks == 0)
      case other => fail(s"expected EqualityFactoring, got $other")
  }

  test("equality factoring: the partner literal need not be eligible") {
    val fx = new Fix; import fx.*
    // `a` is interned first, so `d` outranks it in precedence.
    val a = const("a"); val d = const("d"); val f = fn("f", 1); val x = v(0)
    val cl = clause(pos(mkEq(app(f, x), a)), pos(mkEq(app(f, x), d)))
    // Literal comparison cancels the shared `f(x)` and compares `a` against `d`, so literal 1 is *strictly*
    // maximal: selection offers only it, and literal 0 is never eligible.
    val flags = order.maximalFlags(cl.literals)
    assert(!flags(0) && flags(1), s"expected literal 1 to be the only maximal literal, got ${flags.mkString(",")}")
    // Bachmair-Ganzinger requires eligibility of the *factored* literal only; the partner is any other
    // positive equality. Drawing the partner from the eligible set too lost this inference entirely, and no
    // other test could see it, since they all pass every literal as eligible.
    val factors = Superposition.equalityFactoring(bank, trail, order, cl, Array(1))
    val expected = factors.find(_.literals.toSet == Set(neg(mkEq(d, a)), pos(mkEq(app(f, x), a))))
    assert(expected.isDefined,
      s"lost the factor `d ≉ a ∨ f(x) ≈ a`; got ${factors.map(_.literals.mkString("[", ", ", "]")).mkString("{", "; ", "}")}")
    expected.get.justification match
      case Justification.EqualityFactoring(p, dropped, _, partner, _) =>
        assert(p == cl && dropped == 1 && partner == 0, s"factored $dropped against $partner, expected 1 against 0")
      case other => fail(s"expected EqualityFactoring, got $other")
  }

  // --- a small refutation composing superposition + equality resolution --------------------------

  test("a UEQ refutation: f(a)≈a and ¬(f(f(a))≈a) reduce to □ via superposition + equality resolution") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val axiom = clause(pos(mkEq(app(f, a), a))) //          f(a) = a
    val goal = clause(neg(mkEq(app(f, app(f, a)), a))) //   f(f(a)) ≠ a   (negated conjecture)
    // step 1: superpose f(a)≈a into f(f(a))≠a at the inner f(a) ([0,0]) ⇒ f(a) ≠ a
    val s1 = superposeAt(axiom, 0, 0, goal, 0, Array(0, 0))
    assert(s1.isDefined && s1.get.literals.toSet == Set(neg(mkEq(app(f, a), a))))
    // step 2: superpose f(a)≈a into f(a)≠a at [0] ⇒ a ≠ a
    val s2 = superposeAt(axiom, 0, 0, s1.get, 0, Array(0))
    assert(s2.isDefined && s2.get.literals.toSet == Set(neg(mkEq(a, a))))
    // step 3: equality resolution on a ≠ a ⇒ □
    val s3 = Superposition.equalityResolution(bank, trail, order, s2.get, Array(0))
    assert(s3.length == 1 && s3.head.isEmpty)
  }
