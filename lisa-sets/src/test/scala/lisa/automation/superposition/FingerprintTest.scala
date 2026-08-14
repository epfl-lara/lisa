package lisa.automation.superposition

import scala.collection.mutable

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Tests for the standalone fingerprint index ([[Fingerprint]] + [[FingerprintIndex]], Phase 5 Step 1). */
class FingerprintTest extends AnyFunSuite:

  class Fix extends TermFixture:

    /** Collect the unifiable candidates of `q` from `idx` into a set. */
    def unif[E](idx: FingerprintIndex[E], q: Term): mutable.LinkedHashSet[E] =
      val s = mutable.LinkedHashSet.empty[E]
      idx.retrieveUnifiable(q)(s += _)
      s

    /** Whether `q` and `t` are fingerprint-compatible at every FP7 position (the descent oracle). */
    def fpCompatible(q: Term, t: Term): Boolean =
      val qf = Fingerprint.compute(bank, q, Fingerprint.FP7Trie)
      val tf = Fingerprint.compute(bank, t, Fingerprint.FP7Trie)
      qf.indices.forall(i => Fingerprint.unifiable(qf(i), tf(i)))

    /** Whether `q` and `t` genuinely unify (two scopes, trail restored). */
    def unifies(q: Term, t: Term): Boolean =
      val saved = trail.save()
      val r = trail.unify(q, 0, t, 1)
      trail.restore(saved)
      r

  import Fingerprint.{AnyVar, BelowVar, NotInTerm}

  // --- fingerprint computation --------------------------------------------------------------------

  test("fingerprint samples the FP7 positions with the right feature kinds") {
    val fx = new Fix; import fx.*
    val f = fn("f", 2); val g = fn("g", 1); val aSym = fn("a", 0); val a = bank.mkConst(aSym)
    val t = app(f, app(g, a), v(0)) // f(g(a), x)
    val fp = Fingerprint.compute(bank, t, Fingerprint.FP7Trie) // positions ε,0,1,0.0,0.1,1.0,1.1
    assert(fp(0) == bank.headSymbol(t).code && fp(0) >= 0) //          ε   → f
    assert(fp(1) == g.code) //                                          0   → g
    assert(fp(2) == AnyVar) //                                          1   → variable x
    assert(fp(3) == aSym.code) //                                       0.0 → a
    assert(fp(4) == NotInTerm) //                                       0.1 → g is unary, no arg 1
    assert(fp(5) == BelowVar && fp(6) == BelowVar) //                   1.* → below the variable x
  }

  test("fingerprint of a constant is the symbol then all NotInTerm; of a variable, AnyVar then BelowVar") {
    val fx = new Fix; import fx.*
    val a = const("a")
    val fa = Fingerprint.compute(bank, a, Fingerprint.FP7Trie)
    assert(fa(0) == fn("a", 0).code && (1 until 7).forall(i => fa(i) == NotInTerm))
    val fv = Fingerprint.compute(bank, v(0), Fingerprint.FP7Trie)
    assert(fv(0) == AnyVar && (1 until 7).forall(i => fv(i) == BelowVar))
  }

  test("single-traversal fingerprint matches a naive per-position sampler (differential)") {
    val fx = new Fix; import fx.*
    // reference: sample each FP7 position by an independent top-down walk (what the trie descent replaces)
    def sampleRef(t: Term, path: Array[Int]): Int =
      var cur = t; var i = 0
      while i < path.length do
        if bank.isVar(cur) then return BelowVar
        if path(i) >= bank.arity(cur) then return NotInTerm
        cur = bank.arg(cur, path(i)); i += 1
      if bank.isVar(cur) then AnyVar else bank.headSymbol(cur).code
    def computeRef(t: Term): Array[Int] = Fingerprint.FP7.map(p => sampleRef(t, p))

    val f = fn("f", 1); val g = fn("g", 2); val h = fn("h", 3); val a = const("a"); val b = const("b")
    val terms = Seq(
      a, v(0), app(f, a), app(f, v(0)), app(g, a, b), app(g, v(0), app(f, b)),
      app(h, a, app(g, v(0), b), v(1)), app(f, app(f, app(f, a))), app(g, app(g, a, b), app(f, v(2)))
    )
    for t <- terms do
      assert(Fingerprint.compute(bank, t, Fingerprint.FP7Trie).sameElements(computeRef(t)), s"mismatch for $t")
  }

  // --- the unification compatibility relation -----------------------------------------------------

  test("unifiable compatibility relation follows the table") {
    val f = 1; val g = 2 // two distinct concrete symbol codes
    // concrete query
    assert(Fingerprint.unifiable(f, f) && !Fingerprint.unifiable(f, g))
    assert(Fingerprint.unifiable(f, AnyVar) && Fingerprint.unifiable(f, BelowVar) && !Fingerprint.unifiable(f, NotInTerm))
    // NotInTerm query
    assert(Fingerprint.unifiable(NotInTerm, NotInTerm) && Fingerprint.unifiable(NotInTerm, BelowVar))
    assert(!Fingerprint.unifiable(NotInTerm, AnyVar) && !Fingerprint.unifiable(NotInTerm, f))
    // AnyVar query: everything except NotInTerm
    assert(Fingerprint.unifiable(AnyVar, f) && Fingerprint.unifiable(AnyVar, AnyVar) && Fingerprint.unifiable(AnyVar, BelowVar))
    assert(!Fingerprint.unifiable(AnyVar, NotInTerm))
    // BelowVar query: everything
    assert(Seq(f, g, AnyVar, BelowVar, NotInTerm).forall(sf => Fingerprint.unifiable(BelowVar, sf)))
  }

  test("unifiable is symmetric") {
    val feats = Seq(1, 2, 3, AnyVar, BelowVar, NotInTerm)
    for a <- feats; b <- feats do
      assert(Fingerprint.unifiable(a, b) == Fingerprint.unifiable(b, a), s"asymmetry at ($a,$b)")
  }

  // --- index retrieval ----------------------------------------------------------------------------

  test("retrieveUnifiable returns the real unifiers and prunes an incompatible top symbol") {
    val fx = new Fix; import fx.*
    val f = fn("f", 2); val g = fn("g", 2); val a = const("a"); val b = const("b")
    val idx = new FingerprintIndex[Term](bank)
    val t1 = app(f, a, b); val t2 = app(f, v(0), b); val t3 = app(g, a, b); val t4 = app(f, a, v(1))
    Seq(t1, t2, t3, t4).foreach(t => idx.insert(t, t))
    val q = app(f, a, b) // unifies with t1 (=), t2 (x↦a), t4 (y↦b); not t3 (g≠f)
    val got = unif(idx, q)
    assert(Set(t1, t2, t4).subsetOf(got.toSet)) // all real unifiers present (no false negatives)
    assert(!got.contains(t3)) //                  different top symbol ⇒ pruned at position ε
  }

  test("a variable query retrieves every stored term (AnyVar at the top is compatible with all)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val a = const("a")
    val idx = new FingerprintIndex[Term](bank)
    val ts = Seq(const("a"), app(f, a), app(g, v(0)), v(5))
    ts.foreach(t => idx.insert(t, t))
    assert(unif(idx, v(9)).toSet == ts.toSet) // bare-variable query ⇒ all
  }

  test("the retrieved candidate set equals the fingerprint-compatibility oracle (descent is exact)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val h = fn("h", 2); val a = const("a"); val b = const("b")
    val idx = new FingerprintIndex[Term](bank)
    val ts = Seq(
      const("a"), const("b"), app(f, a), app(f, b), app(f, v(0)), app(g, a),
      app(h, a, b), app(h, v(0), b), app(h, a, v(1)), app(h, v(0), v(1)),
      app(h, app(f, a), b), app(h, a, app(f, b)), v(7)
    )
    ts.foreach(t => idx.insert(t, t))
    for q <- ts do
      val expected = ts.filter(t => fpCompatible(q, t)).toSet
      assert(unif(idx, q).toSet == expected, s"mismatch for query $q")
  }

  test("no false negatives vs real unification: every genuine unifier is a retrieved candidate") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val g = fn("g", 1); val h = fn("h", 2); val a = const("a"); val b = const("b")
    val idx = new FingerprintIndex[Term](bank)
    val ts = Seq(
      const("a"), const("b"), app(f, a), app(f, b), app(f, v(0)), app(g, a),
      app(h, a, b), app(h, v(0), b), app(h, a, v(1)), app(h, v(0), v(1)),
      app(h, app(f, a), b), app(h, a, app(f, b)), app(f, app(g, v(0))), v(7)
    )
    ts.foreach(t => idx.insert(t, t))
    for q <- ts; t <- ts do
      if unifies(q, t) then assert(unif(idx, q).contains(t), s"$t unifies with $q but was not retrieved")
  }

  // --- insertion / deletion -----------------------------------------------------------------------

  test("remove deletes the entry, shrinks size, and leaves the rest retrievable; pruning empties the index") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val idx = new FingerprintIndex[Term](bank)
    val fa = app(f, a); val fx0 = app(f, v(0))
    idx.insert(fa, fa); idx.insert(fx0, fx0)
    assert(idx.size == 2 && unif(idx, fa).toSet == Set(fa, fx0))
    assert(idx.remove(fa, fa) && idx.size == 1)
    assert(unif(idx, fa).toSet == Set(fx0)) // fa gone; fx0 still matches the query f(a)
    assert(!idx.remove(fa, fa)) //             removing again finds nothing
    assert(idx.remove(fx0, fx0) && idx.isEmpty)
  }

  test("removing an absent entry returns false and does not change size") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a"); val b = const("b")
    val idx = new FingerprintIndex[Term](bank)
    idx.insert(app(f, a), app(f, a))
    assert(!idx.remove(app(f, b), app(f, b)) && idx.size == 1) // never inserted
  }

  test("a duplicate (term, entry) insert does not double-count size (isEmpty stays correct after removal)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val idx = new FingerprintIndex[Term](bank)
    val fa = app(f, a)
    idx.insert(fa, fa); idx.insert(fa, fa) //   same (term, entry) twice: the second `add` is a no-op on the bucket
    assert(idx.size == 1) //                     so it must NOT increment _size (regression: was 2)
    assert(idx.remove(fa, fa)) //                a single remove empties the (single) entry
    assert(idx.size == 0 && idx.isEmpty) //      _size back to 0, not stuck at 1
  }

  test("a re-entrant term-keyed op inside a retrieveUnifiable visit fails loudly (shared-buffer guard)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a"); val b = const("b")
    val idx = new FingerprintIndex[Term](bank)
    val fa = app(f, a); val fb = app(f, b)
    idx.insert(fa, fa)
    // A callback that mutates or re-queries the SAME index mid-descent would corrupt the shared fpBuf.
    assertThrows[IllegalStateException] { idx.retrieveUnifiable(fa) { _ => idx.insert(fb, fb) } }
    assertThrows[IllegalStateException] { idx.retrieveUnifiable(fa) { _ => idx.remove(fa, fa) } }
    assertThrows[IllegalStateException] { idx.retrieveUnifiable(fa) { _ => idx.retrieveUnifiable(fa)(_ => ()) } }
    // The guard is released on exit, so sequential (non-nested) retrievals remain fine.
    assert(unif(idx, fa).toSet == Set(fa) && unif(idx, fa).toSet == Set(fa))
  }

  test("a large collision bucket stays correct (insert/retrieve/remove)") {
    val fx = new Fix; import fx.*
    val f = fn("f", 1); val a = const("a")
    val t = app(f, a) // one term, many distinct Int payloads ⇒ all share t's fingerprint ⇒ one big bucket
    val idx = new FingerprintIndex[Int](bank)
    val n = 50
    for i <- 0 until n do idx.insert(t, i)
    assert(idx.size == n)
    def got(): Set[Int] = { val s = mutable.Set.empty[Int]; idx.retrieveUnifiable(t)(s += _); s.toSet }
    assert(got() == (0 until n).toSet) //                         all retrievable after the upgrade
    assert(idx.remove(t, 5) && idx.remove(t, 40) && !idx.remove(t, 999)) // O(1) removal from the hash-set bucket
    assert(idx.size == n - 2 && got() == (0 until n).toSet -- Set(5, 40))
    for i <- 0 until n do idx.remove(t, i) // drains the bucket (5, 40 already gone ⇒ no-ops)
    assert(idx.isEmpty && got().isEmpty)
  }

  // --- payload classes ----------------------------------------------------------------------------

  test("IntoEntry / FromEntry have value equality, so the index removes them by a re-derived value") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a")
    val c = bank.mkClause(Array(bank.mkLiteral(app(P, app(f, a)), true))) // P(f(a))
    val fa = app(f, a)

    val e1 = new IntoEntry(c, 0, Array(0, 0)); val e2 = new IntoEntry(c, 0, Array(0, 0))
    assert(e1 == e2 && e1.hashCode == e2.hashCode && (e1 ne e2)) // equal by value, distinct instances
    assert(e1 != new IntoEntry(c, 0, Array(0)) && e1 != new IntoEntry(c, 1, Array(0, 0)))

    val idx = new FingerprintIndex[IntoEntry](bank)
    idx.insert(fa, e1)
    assert(idx.remove(fa, e2) && idx.isEmpty) // removed via the equal-but-distinct e2

    val g1 = new FromEntry(c, 0, 0); val g2 = new FromEntry(c, 0, 0)
    assert(g1 == g2 && g1.hashCode == g2.hashCode && g1 != new FromEntry(c, 0, 1))
    val fidx = new FingerprintIndex[FromEntry](bank)
    fidx.insert(fa, g1)
    assert(fidx.remove(fa, g2) && fidx.isEmpty)
  }
