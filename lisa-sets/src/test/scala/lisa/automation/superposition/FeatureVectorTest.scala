package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Phase 5 Step 3 (sub-steps 1–2): standalone tests for [[Permutation]] (adaptive feature selection) and
 *  [[FeatureVectorIndex]] (the subsumption feature-vector trie). No saturation-loop wiring yet. */
class FeatureVectorTest extends AnyFunSuite:

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

  // componentwise ≤ on equal-length vectors
  private def le(a: Array[Int], b: Array[Int]): Boolean = a.length == b.length && a.indices.forall(i => a(i) <= b(i))
  private def ge(a: Array[Int], b: Array[Int]): Boolean = le(b, a)

  private def collect(f: (Clause => Unit) => Unit): Set[Int] =
    val s = scala.collection.mutable.Set.empty[Int]
    f(c => s += c.id)
    s.toSet

  // ── FeatureVector.binaryEntropy ────────────────────────────────────────────────────────────────

  test("binaryEntropy: 0 at the extremes, 1 at the balanced split, symmetric") {
    assert(FeatureVector.binaryEntropy(0.0) == 0.0)
    assert(FeatureVector.binaryEntropy(1.0) == 0.0)
    assert(math.abs(FeatureVector.binaryEntropy(0.5) - 1.0) < 1e-9)
    assert(math.abs(FeatureVector.binaryEntropy(0.25) - FeatureVector.binaryEntropy(0.75)) < 1e-9)
    assert(FeatureVector.binaryEntropy(0.5) > FeatureVector.binaryEntropy(0.1))
  }

  // ── Permutation.build (adaptive selection) ─────────────────────────────────────────────────────

  test("Permutation.build leads with pos/neg counts and drops uninformative (all-or-nothing) symbols") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val b = const("b")
    // P is in ALL four clauses (constant ⇒ dropped); Q is in exactly two (balanced ⇒ kept).
    val cs = Seq(
      clause(pos(app(P, a))),
      clause(pos(app(P, b))),
      clause(pos(app(P, a)), pos(app(Q, a))),
      clause(pos(app(P, b)), pos(app(Q, b)))
    )
    val perm = Permutation.build(bank, cs, maxLen = 8)
    assert(perm.sources.take(2).sameElements(Array(FeatureVector.PosCount, FeatureVector.NegCount)))
    assert(perm.sources.contains(Q.code), "balanced symbol Q should be featured")
    assert(!perm.sources.contains(P.code), "ubiquitous symbol P should be dropped as uninformative")
  }

  test("Permutation.build respects maxLen and is deterministic") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val Q = pred("Q", 1); val R = pred("R", 1)
    val a = const("a"); val b = const("b"); val c = const("c")
    val cs = Seq(
      clause(pos(app(P, a))), clause(pos(app(Q, b))), clause(pos(app(R, c))),
      clause(pos(app(P, a)), pos(app(Q, b)))
    )
    val p1 = Permutation.build(bank, cs, maxLen = 4)
    val p2 = Permutation.build(bank, cs, maxLen = 4)
    assert(p1.length == 4)
    assert(p1.sources.sameElements(p2.sources), "same inputs ⇒ same permutation")
  }

  // ── fillVector correctness ─────────────────────────────────────────────────────────────────────

  test("fillVector computes pos/neg counts and per-symbol occurrence counts") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val perm = new Permutation(Array(FeatureVector.PosCount, FeatureVector.NegCount, P.code, f.code), sig.size)
    // { P(f(a)), P(b) } : 2 positive / 0 negative literals; P occurs twice; f occurs once.
    val cl = clause(pos(app(P, app(f, a))), pos(app(P, b)))
    assert(perm.vectorOf(bank, cl).sameElements(Array(2, 0, 2, 1)))
  }

  // ── monotonicity: c subsumes d ⇒ vector(c) ≤ vector(d) ─────────────────────────────────────────

  test("feature vectors are monotone under subsumption (the completeness invariant)") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val Q = pred("Q", 1); val f = fn("f", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    val perm = new Permutation(Array(FeatureVector.PosCount, FeatureVector.NegCount, P.code, Q.code, f.code), sig.size)
    val pairs: Seq[(Clause, Clause)] = Seq(
      (clause(pos(app(P, x))), clause(pos(app(P, a)))),                          // P(x) ⊑ P(a)
      (clause(pos(app(P, x))), clause(pos(app(P, a)), pos(app(Q, b)))),          // extra literal grows counts
      (clause(pos(app(P, x))), clause(pos(app(P, app(f, a))))),                  // x↦f(a) grows the f count
      (clause(neg(app(P, x)), pos(app(Q, x))), clause(neg(app(P, a)), pos(app(Q, a)))) // multi-literal
    )
    for (c, d) <- pairs do
      assert(Subsumption.subsumes(bank, trail, c, d), s"precondition: c must subsume d")
      assert(le(perm.vectorOf(bank, c), perm.vectorOf(bank, d)),
        s"vector(${perm.vectorOf(bank, c).mkString(",")}) ≰ vector(${perm.vectorOf(bank, d).mkString(",")})")
  }

  test("randomized: subsumption implies feature-vector ≤ over many generated pairs (monotonicity)") {
    val fx = new Fix; import fx.*
    val rnd = new scala.util.Random(20260718L)
    val preds: Array[Symbol] = (0 until 6).map(i => pred(s"P$i", 1)).toArray
    val funcs: Array[Symbol] = (0 until 3).map(i => fn(s"g$i", 1)).toArray
    val consts: Array[Term] = (0 until 4).map(i => const(s"k$i")).toArray
    // A permutation over EVERY symbol, so every vector component is exercised by the property.
    val perm = new Permutation(Array(FeatureVector.PosCount, FeatureVector.NegCount) ++ (0 until sig.size).toArray, sig.size)

    def ground(depth: Int): Term =
      if depth <= 0 || rnd.nextInt(3) == 0 then consts(rnd.nextInt(consts.length))
      else app(funcs(rnd.nextInt(funcs.length)), ground(depth - 1))

    var n = 0
    while n < 400 do
      // d: k distinct-predicate ground literals (random signs).
      val k = 1 + rnd.nextInt(4)
      val chosenPreds = rnd.shuffle((0 until preds.length).toList).take(k)
      val dParts = chosenPreds.map(pi => (pi, rnd.nextBoolean(), ground(2)))
      val d = clause(dParts.map { case (pi, s, t) => if s then pos(app(preds(pi), t)) else neg(app(preds(pi), t)) }*)
      // c: a non-empty subset of d's literals, each optionally generalized (whole argument → a FRESH variable),
      //    same predicate + sign. c then subsumes d (sub-multiset + generalization; distinct preds ⇒ injective).
      val subset = { val s = dParts.filter(_ => rnd.nextBoolean()); if s.isEmpty then List(dParts(rnd.nextInt(dParts.length))) else s }
      var vi = 0
      val c = clause(subset.map { case (pi, s, t) =>
        val atom = if rnd.nextBoolean() then { val a = app(preds(pi), v(vi)); vi += 1; a } else app(preds(pi), t)
        if s then pos(atom) else neg(atom)
      }*)
      assert(Subsumption.subsumes(bank, trail, c, d), s"generator precondition: c must subsume d (n=$n)")
      assert(le(perm.vectorOf(bank, c), perm.vectorOf(bank, d)),
        s"monotonicity violated (n=$n): ${perm.vectorOf(bank, c).mkString(",")} ≰ ${perm.vectorOf(bank, d).mkString(",")}")
      n += 1
  }

  // ── FeatureVectorIndex retrieval vs a brute-force oracle ───────────────────────────────────────

  private def sampleClauses(fx: Fix): Seq[Clause] =
    import fx.*
    val P = pred("P", 1); val Q = pred("Q", 1); val R = pred("R", 1); val f = fn("f", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    Seq(
      clause(pos(app(P, x))),
      clause(pos(app(P, a))),
      clause(pos(app(P, a)), pos(app(Q, b))),
      clause(pos(app(P, app(f, a)))),
      clause(neg(app(P, a)), pos(app(Q, a))),
      clause(pos(app(Q, b))),
      clause(pos(app(P, a)), neg(app(R, b))),
      clause(pos(app(P, b)), pos(app(Q, a))), // shares its vector shape with #3 ⇒ leaf-bucket collision
      clause(neg(app(R, x)))
    )

  test("forwardCandidates returns exactly the ≤-cone (matches a brute-force oracle)") {
    val fx = new Fix
    val cs = sampleClauses(fx)
    val perm = Permutation.build(fx.bank, cs, maxLen = 8)
    val idx = new FeatureVectorIndex(fx.bank, perm)
    cs.foreach(idx.insert)
    val vec = cs.map(c => c -> perm.vectorOf(fx.bank, c)).toMap
    for q <- cs do
      val oracle = cs.filter(c => le(vec(c), vec(q))).map(_.id).toSet
      assert(collect(idx.forwardCandidates(q)) == oracle, s"forward mismatch for q=${q.id}")
  }

  test("backwardCandidates returns exactly the ≥-cone (matches a brute-force oracle)") {
    val fx = new Fix
    val cs = sampleClauses(fx)
    val perm = Permutation.build(fx.bank, cs, maxLen = 8)
    val idx = new FeatureVectorIndex(fx.bank, perm)
    cs.foreach(idx.insert)
    val vec = cs.map(c => c -> perm.vectorOf(fx.bank, c)).toMap
    for q <- cs do
      val oracle = cs.filter(c => ge(vec(c), vec(q))).map(_.id).toSet
      assert(collect(idx.backwardCandidates(q)) == oracle, s"backward mismatch for q=${q.id}")
  }

  test("backwardCandidatesThenInsert queries the ≥-cone of the pre-insert set (excluding q), then inserts q") {
    val fx = new Fix
    val cs = sampleClauses(fx)
    val perm = Permutation.build(fx.bank, cs, maxLen = 8)
    val idx = new FeatureVectorIndex(fx.bank, perm)
    val q = cs.head
    val stored = cs.tail
    stored.foreach(idx.insert)
    val vec = cs.map(c => c -> perm.vectorOf(fx.bank, c)).toMap
    // fused op: backward query runs over the stored set (q not yet present), then q is inserted (side effect)
    val visited = collect(idx.backwardCandidatesThenInsert(q))
    assert(visited == stored.filter(c => ge(vec(c), vec(q))).map(_.id).toSet, "must see exactly the ≥-cone, without q")
    assert(idx.size == cs.size, "q must have been inserted")
    assert(collect(idx.forwardCandidates(q)).contains(q.id), "q is now retrievable")
  }

  // ── insert / remove / prune / size ─────────────────────────────────────────────────────────────

  test("insert/remove maintain size and retrieval; removed clauses vanish; re-add works") {
    val fx = new Fix
    val cs = sampleClauses(fx)
    val perm = Permutation.build(fx.bank, cs, maxLen = 8)
    val idx = new FeatureVectorIndex(fx.bank, perm)
    cs.foreach(idx.insert)
    assert(idx.size == cs.size)

    val victim = cs(2)
    assert(idx.remove(victim))
    assert(idx.size == cs.size - 1)
    // victim no longer appears as a candidate of itself (forward includes equal vectors)
    assert(!collect(idx.forwardCandidates(victim)).contains(victim.id))
    assert(!idx.remove(victim), "removing an absent clause returns false")

    idx.insert(victim)
    assert(idx.size == cs.size)
    assert(collect(idx.forwardCandidates(victim)).contains(victim.id))
  }

  test("clear empties the index") {
    val fx = new Fix
    val cs = sampleClauses(fx)
    val perm = Permutation.build(fx.bank, cs, maxLen = 8)
    val idx = new FeatureVectorIndex(fx.bank, perm)
    cs.foreach(idx.insert)
    idx.clear()
    assert(idx.isEmpty && idx.size == 0)
    assert(collect(idx.forwardCandidates(cs.head)).isEmpty)
  }

  test("a fully collapsed permutation (no informative features) degenerates to one leaf but stays correct") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val b = const("b")
    // Both clauses contain P, Q, a, b ⇒ every symbol is ubiquitous (dropped) and pos/neg counts match ⇒ identical
    // vectors, distinct content: they collide in one leaf bucket.
    val cs = Seq(clause(pos(app(P, a)), pos(app(Q, b))), clause(pos(app(P, b)), pos(app(Q, a))))
    val perm = Permutation.build(bank, cs, maxLen = 8)
    assert(perm.sources.sameElements(Array(FeatureVector.PosCount, FeatureVector.NegCount)), "all symbols uninformative")
    val idx = new FeatureVectorIndex(bank, perm)
    cs.foreach(idx.insert)
    // both share the single leaf; a forward query returns both (the verifier would then separate them)
    assert(collect(idx.forwardCandidates(cs.head)) == cs.map(_.id).toSet)
  }
