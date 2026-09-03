package lisa.automation.superposition

import lisa.automation.superposition.index._
import org.scalatest.funsuite.AnyFunSuite

import Core._
import Demodulation.Rule

/**
 * Standalone tests for the **perfect** [[DiscriminationTree]], the forward-demodulation generalization
 *  index, exercised directly rather than through the saturation loop that uses it.
 */
class DiscriminationTreeTest extends AnyFunSuite:

  class Fix extends TermFixture:

    /**
     * A demodulator `lhs → rhs`; a fresh source clause gives it a distinct id (for removal by (source.id, side)).
     */
    def rule(lhs: Term, rhs: Term): Rule =
      val src = bank.mkClause(Array(bank.mkLiteral(mkEq(lhs, rhs), true)))
      new Rule(src, 0, lhs, rhs, oriented = true, lhsVars = Array.empty[Term])

    /**
     * Does `r.lhs` really match onto `u`? (the exact relation the perfect tree computes.)
     */
    def matches(r: Rule, u: Term): Boolean =
      val s = trail.save()
      val ok = trail.matchTerm(r.lhs, 0, u, 1)
      trail.restore(s)
      ok

    def tree: DiscriminationTree[Rule] = new DiscriminationTree(bank, trail)

  /**
   * The tree is generic in its payload, so a rule is stored under its own left side, as `ActiveSet` does.
   */
  extension (t: DiscriminationTree[Rule])
    def insertRule(r: Rule): Unit = t.insert(r.lhs, r)
    def removeRule(r: Rule): Boolean = t.remove(r.lhs, r)

  private def collect(f: (Rule => Boolean) => Boolean): Set[Int] =
    val s = scala.collection.mutable.Set.empty[Int]
    f(r => { s += r.source.id; false })
    s.toSet

  // ── the perfect tree returns EXACTLY the true generalizations ───────────────────────────────────

  test("retrieveGeneralizations returns exactly the LHSs that match (perfect: no false negatives or positives)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val h = fn("h", 2)
    val a = const("a"); val b = const("b")
    val x = v(0); val y = v(1)
    val rules = Seq(
      rule(app(f, x), a), // f(X) → a
      rule(app(f, a), b), // f(a) → b
      rule(app(f, app(g, x)), b), // f(g(X)) → b
      rule(app(g, x), a), // g(X) → a
      rule(app(h, x, x), a), // h(X,X) → a  (nonlinear: matched only on equal args)
      rule(app(h, x, y), b) // h(X,Y) → b
    )
    val t = tree; rules.foreach(t.insertRule)
    assert(t.size == rules.size)
    val queries = Seq(
      app(f, a),
      app(f, b),
      app(f, app(g, a)),
      app(g, b),
      app(h, a, a),
      app(h, a, b),
      app(f, app(f, a)),
      a,
      app(f, x)
    )
    for u <- queries do
      val expected = rules.filter(r => matches(r, u)).map(_.source.id).toSet
      assert(collect(t.retrieveGeneralizations(u)) == expected, s"mismatch for query $u")
  }

  test("skeleton discrimination: symbol structure selects the right LHSs") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val x = v(0)
    val rF = rule(app(f, x), a); val rFa = rule(app(f, a), a); val rFg = rule(app(f, app(g, x)), a); val rG = rule(app(g, x), a)
    val t = tree; Seq(rF, rFa, rFg, rG).foreach(t.insertRule)
    assert(collect(t.retrieveGeneralizations(app(f, a))) == Set(rF.source.id, rFa.source.id))
    assert(collect(t.retrieveGeneralizations(app(f, app(g, a)))) == Set(rF.source.id, rFg.source.id))
  }

  test("nonlinear LHS matches only when the repeated variable's occurrences agree (checked during descent)") {
    val fx = new Fix; import fx.*
    val h = fn("h", 2); val a = const("a"); val b = const("b"); val x = v(0)
    val rNL = rule(app(h, x, x), a) // h(X,X)
    val t = tree; t.insertRule(rNL)
    assert(collect(t.retrieveGeneralizations(app(h, a, a))) == Set(rNL.source.id)) // equal args: matches
    assert(collect(t.retrieveGeneralizations(app(h, a, b))).isEmpty) // distinct args: rejected
  }

  test("a matching leaf leaves σ live on the trail (rσ is buildable during visit)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a"); val x = v(0)
    val r = rule(app(f, x), x) // f(X) → X
    val t = tree; t.insertRule(r)
    var applied: Option[Term] = None
    t.retrieveGeneralizations(app(f, a)) { rl =>
      // σ = {X ↦ a} is on the trail here; applying it to the RHS (X) must give `a`
      applied = Some(trail.applier().apply(rl.rhs, 0))
      true // stop after the first
    }
    assert(applied.contains(a), s"expected rσ = a, got $applied")
  }

  test("ground fast path: a whole ground LHS matches only its identical query, and coexists with variable LHSs") {
    val fx = new Fix; import fx.*
    val g = fn("g", 1); val a = const("a"); val b = const("b"); val x = v(0)
    val rGa = rule(app(g, app(g, a)), b) // g(g(a)) → b   (fully ground ⇒ one ground edge)
    val rGx = rule(app(g, x), a) // g(x) → a
    val t = tree; t.insertRule(rGa); t.insertRule(rGx)
    // g(g(a)) matches the ground LHS (exact) and g(x) [x = g(a)]
    assert(collect(t.retrieveGeneralizations(app(g, app(g, a)))) == Set(rGa.source.id, rGx.source.id))
    // g(g(b)) matches only g(x); the ground LHS g(g(a)) is not identical to it
    assert(collect(t.retrieveGeneralizations(app(g, app(g, b)))) == Set(rGx.source.id))
    // removing the ground rule prunes its ground edge; g(g(a)) then matches only g(x)
    assert(t.removeRule(rGa))
    assert(collect(t.retrieveGeneralizations(app(g, app(g, a)))) == Set(rGx.source.id))
  }

  // ── size pruning does not drop valid matches ────────────────────────────────────────────────────

  test("size pruning keeps every true match (heavy and light demodulators mixed)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val a = const("a"); val x = v(0)
    val light = rule(app(f, x), a)
    val heavy = rule(app(f, app(g, app(g, x))), a)
    val t = tree; t.insertRule(light); t.insertRule(heavy)
    assert(collect(t.retrieveGeneralizations(app(f, a))) == Set(light.source.id))
    assert(collect(t.retrieveGeneralizations(app(f, app(g, app(g, a))))) == Set(light.source.id, heavy.source.id))
  }

  // ── insert / remove / prune / size ──────────────────────────────────────────────────────────────

  test("remove drops a demodulator, prunes its path, and leaves the rest retrievable") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a"); val x = v(0)
    val rF = rule(app(f, x), a); val rFa = rule(app(f, a), a)
    val t = tree; t.insertRule(rF); t.insertRule(rFa)
    assert(t.size == 2)
    assert(t.removeRule(rFa))
    assert(t.size == 1)
    assert(collect(t.retrieveGeneralizations(app(f, a))) == Set(rF.source.id))
    assert(!t.removeRule(rFa), "removing an absent rule returns false")
    t.insertRule(rFa)
    assert(collect(t.retrieveGeneralizations(app(f, a))) == Set(rF.source.id, rFa.source.id))
  }

  /**
   * The `visit` contract. Unlike the two clause indices, where a corrupted shared buffer costs a *dropped*
   * candidate, corrupting this one is unsound: `qLen` would be reset to the inner query's length, the outer
   * descent would reach `i == qLen` having consumed only a prefix of its own query, and `visit` would be
   * handed rules whose LHS does not generalize it, with a partial σ live on the trail. So it throws.
   */
  test("re-entering the tree from inside a retrieval callback fails loudly") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a"); val b = const("b"); val x = v(0)
    val t = tree
    val r = rule(app(f, x), a)
    t.insertRule(r)
    for (label, reenter) <- Seq[(String, Rule => Unit)](
        "retrieveGeneralizations" -> (_ => t.retrieveGeneralizations(app(f, b))(_ => false)),
        "insert" -> (_ => t.insertRule(rule(app(f, x), b))),
        "remove" -> (rr => { t.removeRule(rr); () })
      )
    do
      val e = intercept[IllegalStateException](t.retrieveGeneralizations(app(f, a)) { rr =>
        reenter(rr); false
      })
      assert(e.getMessage.contains(label), s"expected the $label re-entry to be named, got: ${e.getMessage}")
    // The guard must disarm afterwards, or every later retrieval would throw too.
    assert(collect(t.retrieveGeneralizations(app(f, a))) == Set(r.source.id), "the guard did not disarm")
  }

  test("a callback that binds cannot leak those bindings into the next rule at the same leaf") {
    val fx = new Fix; import fx.*
    // Two demodulators sharing one LHS, so they sit at the *same* leaf and are visited under the same σ.
    val f = fn("f", 1); val a = const("a"); val b = const("b"); val c = const("c"); val x = v(0)
    val t = tree
    t.insertRule(rule(app(f, x), a))
    t.insertRule(rule(app(f, x), b))
    // The trail checkpoint at the start of each visit must be identical: σ (x ↦ c) is established by the
    // descent before the leaf, and nothing a previous callback did may still be on the trail.
    var checkpoints = List.empty[Int]
    var first = true
    t.retrieveGeneralizations(app(f, c)) { _ =>
      checkpoints ::= trail.save()
      if first then { trail.matchTerm(v(1), 0, a, 1); first = false } // a stray binding, deliberately unrestored
      false
    }
    assert(checkpoints.length == 2, s"expected both rules at the leaf to be visited, got ${checkpoints.length}")
    assert(checkpoints.distinct.length == 1, s"a binding leaked between rules at one leaf: trail checkpoints ${checkpoints.reverse.mkString(", ")}")
  }
