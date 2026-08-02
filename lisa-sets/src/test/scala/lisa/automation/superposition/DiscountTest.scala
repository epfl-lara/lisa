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
    bank.selector = new CompleteBestLiteralSelector(bank.order)
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
    bank.selector = new CompleteBestLiteralSelector(bank.order)
    val p = pred("P", 1); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
    val cs = Seq(
      clause(pos(app(p, x)), pos(app(p, y))), //  P(x) ∨ P(y) -- both maximal, both selected
      clause(neg(app(p, a)), neg(app(p, b))) //  ¬P(a) ∨ ¬P(b)
    )
    assert(discount.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  test("the factoring after-check still refutes the factoring problem") {
    val fx = new Fix; import fx.*
    bank.selector = new CompleteBestLiteralSelector(bank.order)
    val p = pred("P", 1); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
    val cs = Seq(clause(pos(app(p, x)), pos(app(p, y))), clause(neg(app(p, a)), neg(app(p, b))))
    val d = new Discount(bank, trail, factorAfterCheck = true)
    assert(d.saturate(cs).isInstanceOf[Discount.Result.Refutation])
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
          case Justification.Superposition(from, _, _, into, _, _) => inputLeaves(from) + inputLeaves(into)
          case Justification.EqualityResolution(par, _) => inputLeaves(par)
          case Justification.EqualityFactoring(par, _, _, _, _) => inputLeaves(par)
          case Justification.Demodulation(t, _, _, ru, _) => inputLeaves(t) + inputLeaves(ru)
        assert(empty.isEmpty)
        assert(inputLeaves(empty) >= 2) // derived from at least two input clauses
      case other => fail(s"expected Refutation, got $other")
  }

  // --- subsumption (Phase 2) ------------------------------------------------------------------

  test("backward subsumption deletes an active clause subsumed by the given") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    // {P(a)} is selected first (equal weight, smaller id), then the more general {P(x)} subsumes it.
    val d = new Discount(bank, trail)
    val r = d.saturate(Seq(clause(pos(app(p, a))), clause(pos(app(p, x)))))
    assert(r == Discount.Result.Saturated)
    assert(d.backwardSubsumed == 1) // {P(x)} backward-subsumes the already-active {P(a)}
    assert(d.forwardSubsumed == 0) // {P(a)} does not subsume {P(x)} (a cannot match the rigid x)
  }

  test("forward subsumption skips a subsumed clause at selection") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // {P(x)} (lighter) is activated first; the heavier {P(a), Q(b)} is then subsumed on selection.
    val d = new Discount(bank, trail)
    val r = d.saturate(Seq(clause(pos(app(p, x))), clause(pos(app(p, a)), pos(app(q, b)))))
    assert(r == Discount.Result.Saturated)
    assert(d.forwardSubsumed == 1) // {P(a), Q(b)} subsumed by the active {P(x)}
    assert(d.backwardSubsumed == 0)
  }

  test("forward subsumption discards a generated clause (addPassive path)") {
    val fx = new Fix; import fx.*
    bank.selector = FirstNegativeSelector // all-positive clauses resolve on their first (canonical) literal
    // `a` is interned first, so it has the smallest symbol code and sorts first under canonicalisation --
    // ensuring the all-positive {a,c} keeps `a` as its selected literal so resolution on a/¬a fires.
    val a = prop("a"); val b = prop("b"); val c = prop("c")
    // {b,c} is activated first; resolving {¬a,b} and {a,c} regenerates {b,c}, which the active {b,c} subsumes.
    // Force forward simplify at generation on (it is off by default) so this exercises the addPassive path.
    val d = new Discount(bank, trail, forwardSimplifyAtGeneration = true)
    val r = d.saturate(Seq(clause(pos(b), pos(c)), clause(neg(a), pos(b)), clause(pos(a), pos(c))))
    assert(r == Discount.Result.Saturated)
    assert(d.forwardSubsumed >= 1) // the resolvent {b,c} is subsumed by the active {b,c} at addPassive
    assert(d.backwardSubsumed == 0)
  }

  test("with both flags off, subsumption is inert (pure simplification)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    // same inputs as the backward-subsumption test, but no simplification: same verdict, no deletions.
    val d = new Discount(bank, trail, forwardSubsumption = false, backwardSubsumption = false)
    val r = d.saturate(Seq(clause(pos(app(p, a))), clause(pos(app(p, x)))))
    assert(r == Discount.Result.Saturated)
    assert(d.forwardSubsumed == 0 && d.backwardSubsumed == 0)
  }

  test("subsumption preserves a refutation verdict (flags on and off agree)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(q, x))), // ¬P(x) ∨ Q(x)
      clause(pos(app(p, a))), //                 P(a)
      clause(neg(app(q, a))) //                  ¬Q(a)
    )
    val on = new Discount(bank, trail, forwardSubsumption = true, backwardSubsumption = true)
    val off = new Discount(bank, trail, forwardSubsumption = false, backwardSubsumption = false)
    assert(on.saturate(cs).isInstanceOf[Discount.Result.Refutation])
    assert(off.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  // --- unit deletion (Phase 2 P1) -------------------------------------------------------------

  test("forward unit deletion shrinks the given at selection") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // {¬P(x)} (lighter) activates first; selecting {P(a), Q(b)} then unit-deletes P(a) -> {Q(b)}.
    val d = new Discount(bank, trail)
    val r = d.saturate(Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x)))))
    assert(r == Discount.Result.Saturated)
    assert(d.forwardUnitDeleted == 1)
    assert(d.backwardUnitDeleted == 0)
  }

  test("backward unit deletion shrinks an active clause") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // Force age (FIFO) selection so {P(a), Q(b)} activates before the lighter unit {¬P(x)}; the unit then
    // backward-unit-deletes P(a) out of the active clause.
    val d = new Discount(bank, trail, ageRatio = 1, weightRatio = 0)
    val r = d.saturate(Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x)))))
    assert(r == Discount.Result.Saturated)
    assert(d.backwardUnitDeleted == 1)
    assert(d.forwardUnitDeleted == 0)
  }

  test("a unit conflict via unit deletion closes the clause to □ (refutation)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // {¬P(x)} deletes P(a) -> {Q(b)}; {¬Q(b)} then deletes Q(b) -> □.
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x))), clause(neg(app(q, b))))
    assert(new Discount(bank, trail).saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  test("with unit-deletion flags off it is inert (pure simplification)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x))))
    val d = new Discount(bank, trail, forwardUnitDeletion = false, backwardUnitDeletion = false)
    assert(d.saturate(cs) == Discount.Result.Saturated)
    assert(d.forwardUnitDeleted == 0 && d.backwardUnitDeleted == 0)
  }

  test("unit deletion preserves a refutation verdict (flags on and off agree)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x))), clause(neg(app(q, b))))
    val on = new Discount(bank, trail, forwardUnitDeletion = true, backwardUnitDeletion = true)
    val off = new Discount(bank, trail, forwardUnitDeletion = false, backwardUnitDeletion = false)
    assert(on.saturate(cs).isInstanceOf[Discount.Result.Refutation])
    assert(off.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  // --- general subsumption resolution (off by default; enabled explicitly here) ----------------

  test("forward general subsumption resolution shrinks the given at selection") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    // {¬P(x), Q(x)} (lighter) activates first; selecting {P(a), Q(a), R(b)} then SR-resolves P(a) → {Q(a), R(b)}.
    val d = new Discount(bank, trail, forwardSubsumptionResolution = true)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b))), clause(neg(app(p, x)), pos(app(q, x))))
    assert(d.saturate(cs) == Discount.Result.Saturated)
    assert(d.forwardSubsumptionResolved == 1)
    assert(d.backwardSubsumptionResolved == 0)
  }

  test("backward general subsumption resolution shrinks an active clause") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    // Force age order so {P(a), Q(a), R(b)} activates before the (multi-literal) side {¬P(x), Q(x)}.
    val d = new Discount(bank, trail, ageRatio = 1, weightRatio = 0, backwardSubsumptionResolution = true)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b))), clause(neg(app(p, x)), pos(app(q, x))))
    assert(d.saturate(cs) == Discount.Result.Saturated)
    assert(d.backwardSubsumptionResolved == 1)
    assert(d.forwardSubsumptionResolved == 0)
  }

  test("general subsumption resolution is off by default and inert when disabled") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b))), clause(neg(app(p, x)), pos(app(q, x))))
    val d = new Discount(bank, trail) // SR flags default false
    assert(d.saturate(cs) == Discount.Result.Saturated)
    assert(d.forwardSubsumptionResolved == 0 && d.backwardSubsumptionResolved == 0)
  }

  // --- condensation (off by default; enabled explicitly here) -----------------------------------

  test("condensation shrinks a clause at creation") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    // {P(x), P(a)} condenses to {P(a)} when it enters passive
    val d = new Discount(bank, trail, condensation = true)
    assert(d.saturate(Seq(clause(pos(app(p, x)), pos(app(p, a))))) == Discount.Result.Saturated)
    assert(d.condensed == 1)
  }

  test("condensation is off by default and inert when disabled") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    val d = new Discount(bank, trail) // condensation defaults false
    assert(d.saturate(Seq(clause(pos(app(p, x)), pos(app(p, a))))) == Discount.Result.Saturated)
    assert(d.condensed == 0)
  }

  test("condensation preserves a refutation verdict (flags on and off agree)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    val cs = Seq(clause(pos(app(p, x)), pos(app(p, a))), clause(neg(app(p, a))))
    val on = new Discount(bank, trail, condensation = true)
    val off = new Discount(bank, trail, condensation = false)
    assert(on.saturate(cs).isInstanceOf[Discount.Result.Refutation])
    assert(off.saturate(cs).isInstanceOf[Discount.Result.Refutation])
  }

  // --- indexed resolution (Phase 5, Step 2): A/B equivalence with the linear scan --------------

  test("fingerprint-indexed resolution and the linear scan reach the same verdict (A/B equivalence)") {
    // The literal indices are a candidate filter confirmed by real unification, so the indexed and linear
    // resolution paths must generate the same inference set, hence the same refuted/saturated verdict (clause
    // ids differ, the outcome does not). Equality is off throughout, so only the resolution path is exercised.
    def cat(r: Discount.Result): String = r match
      case _: Discount.Result.Refutation => "refuted"
      case Discount.Result.Saturated     => "saturated"
      case Discount.Result.Unknown       => "unknown"
    def verdict(indexed: Boolean, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, equality = false, fingerprintIndexing = indexed).saturate(cs, maxGiven = 5000))

    val builders: Seq[(String, Fix => Seq[Clause])] = Seq(
      "propositional P, ¬P" -> { fx => import fx.*; val p = prop("P"); Seq(clause(pos(p)), clause(neg(p))) },
      "propositional chain ¬P∨Q, ¬Q∨R, P, ¬R" -> { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(neg(p), pos(q)), clause(neg(q), pos(r)), clause(pos(p)), clause(neg(r))) },
      "first-order ¬P(x)∨Q(x), P(a), ¬Q(a)" -> { fx => import fx.*
        val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(p, x)), pos(app(q, x))), clause(pos(app(p, a))), clause(neg(app(q, a)))) },
      "multi-predicate mix ¬P(x)∨¬Q(x)∨R(x), P(a), Q(a), ¬R(a)" -> { fx => import fx.*
        val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(p, x)), neg(app(q, x)), pos(app(r, x))),
            clause(pos(app(p, a))), clause(pos(app(q, a))), clause(neg(app(r, a)))) },
      "needs factoring P(x)∨P(y), ¬P(a)∨¬P(b)" -> { fx => import fx.*
        val p = pred("P", 1); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
        Seq(clause(pos(app(p, x)), pos(app(p, y))), clause(neg(app(p, a)), neg(app(p, b)))) },
      "self-resolvable ¬P(x)∨P(f(x)), P(a), ¬P(f(f(a)))" -> { fx => import fx.*
        val p = pred("P", 1); val f = fn("f", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(p, x)), pos(app(p, app(f, x)))), clause(pos(app(p, a))), clause(neg(app(p, app(f, app(f, a)))))) },
      "satisfiable P(a), Q(b)" -> { fx => import fx.*
        val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
        Seq(clause(pos(app(p, a))), clause(pos(app(q, b)))) }
    )
    for (name, b) <- builders do
      assert(verdict(indexed = true, b) == verdict(indexed = false, b), s"index vs scan verdict differ on: $name")
  }

  // --- feature-vector subsumption index (Phase 5, Step 3): A/B equivalence with the linear scan ---

  test("feature-vector subsumption and the linear scan reach the same verdict (A/B equivalence)") {
    // The feature-vector index is a superset filter confirmed by the real `Subsumption.subsumes`, and its features
    // are subsumption-monotone, so the indexed and scanned simplification paths must reach the same verdict.
    def cat(r: Discount.Result): String = r match
      case _: Discount.Result.Refutation => "refuted"
      case Discount.Result.Saturated     => "saturated"
      case Discount.Result.Unknown       => "unknown"
    def verdict(indexed: Boolean, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, equality = false, subsumptionIndexing = indexed).saturate(cs, maxGiven = 5000))

    val builders: Seq[(String, Fix => Seq[Clause])] = Seq(
      "unit subsumes a longer clause, then refute" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val b = const("b"); val c = const("c"); val x = v(0)
        Seq(clause(pos(app(P, x))), clause(pos(app(P, a)), pos(app(Q, b))), clause(neg(app(P, c)))) },
      "satisfiable with redundant instances (forward subsumption)" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
        Seq(clause(pos(app(P, x))), clause(pos(app(P, a))), clause(pos(app(Q, b)))) },
      "first-order resolution refutation" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))), clause(pos(app(P, a))), clause(neg(app(Q, a)))) },
      "propositional chain" -> { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(neg(p), pos(q)), clause(neg(q), pos(r)), clause(pos(p)), clause(neg(r))) },
      "backward subsumption (general activates after instance), then refute" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val d = const("d"); val x = v(0)
        Seq(clause(pos(app(P, a)), pos(app(Q, a))), clause(pos(app(P, x))), clause(neg(app(P, d)))) },
      "unit deletion shrinks then closes" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a")
        Seq(clause(pos(app(P, a))), clause(neg(app(P, a)), pos(app(Q, a))), clause(neg(app(Q, a)))) }
    )
    for (name, b) <- builders do
      assert(verdict(indexed = true, b) == verdict(indexed = false, b), s"subsumption index vs scan verdict differ on: $name")
  }

  // --- forward unit deletion: {¬K} index dispatch vs the activeUnits scan (Phase 5, Step 4) A/B ---

  test("forward unit deletion: the {¬K} index dispatch and the activeUnits scan reach the same verdict (A/B)") {
    // Both forward-unit-deletion paths delete the same literals (complete candidate sets verified by the same
    // `subsumptionResolutionResolvent`), so forcing the index dispatch (threshold 0) vs the scan (threshold ∞)
    // must reach the same verdict. Both run with `subsumptionIndexing = true` so only the unit-deletion sub-path
    // differs.
    def cat(r: Discount.Result): String = r match
      case _: Discount.Result.Refutation => "refuted"
      case Discount.Result.Saturated     => "saturated"
      case Discount.Result.Unknown       => "unknown"
    def verdict(threshold: Int, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, equality = false, subsumptionIndexing = true,
        forwardUnitDeletionIndexThreshold = threshold).saturate(cs, maxGiven = 5000))

    val builders: Seq[(String, Fix => Seq[Clause])] = Seq(
      "unit deletion shrinks then closes" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a")
        Seq(clause(pos(app(P, a))), clause(neg(app(P, a)), pos(app(Q, a))), clause(neg(app(Q, a)))) },
      "general unit deletes an instance literal, then closes" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(pos(app(P, x))), clause(neg(app(P, a)), pos(app(Q, a))), clause(neg(app(Q, a)))) },
      "no unit deletes anything (index branch is a no-op)" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))), clause(pos(app(P, a))), clause(neg(app(Q, a)))) }
    )
    for (name, b) <- builders do
      assert(verdict(threshold = 0, b) == verdict(threshold = Int.MaxValue, b), s"index dispatch vs scan verdict differ on: $name")
  }

  // --- backward general subsumption resolution: sign-flip index vs the active scan (Phase 5, Step 4) A/B ---

  test("backward general subsumption resolution: the sign-flip index and the scan reach the same verdict (A/B)") {
    // With backward SR on, the indexed path flips each literal of `gc` and queries the feature-vector index (its
    // ≥-cone = candidate subsumees), while the scan iterates `active`. Both apply the same
    // `subsumptionResolutionResolvent`, and the union of the flipped-clause ≥-cones is a complete superset of the
    // SR victims, so the verdicts must match.
    def cat(r: Discount.Result): String = r match
      case _: Discount.Result.Refutation => "refuted"
      case Discount.Result.Saturated     => "saturated"
      case Discount.Result.Unknown       => "unknown"
    def verdict(indexed: Boolean, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, equality = false, subsumptionIndexing = indexed,
        backwardSubsumptionResolution = true, forwardSubsumptionResolution = true).saturate(cs, maxGiven = 5000))

    val builders: Seq[(String, Fix => Seq[Clause])] = Seq(
      "2-literal clause SR-resolves a literal of an active clause, then refute" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val R = pred("R", 1); val a = const("a"); val b = const("b"); val x = v(0)
        // {¬P(x), Q(x)} SR-resolves {P(a), Q(a), R(b)} on P(a) (rest {Q(x)}→{Q(a)} ⊆ target), deleting P(a).
        Seq(clause(pos(app(P, a)), pos(app(Q, a)), pos(app(R, b))),
            clause(neg(app(P, x)), pos(app(Q, x))),
            clause(neg(app(Q, a))), clause(neg(app(R, b)))) },
      "propositional 2-literal SR chain" -> { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(pos(p), pos(q)), clause(neg(p), pos(r)), clause(neg(q)), clause(neg(r))) },
      "no SR applies (both paths are no-ops)" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))), clause(pos(app(P, a))), clause(neg(app(Q, a)))) }
    )
    for (name, b) <- builders do
      assert(verdict(indexed = true, b) == verdict(indexed = false, b), s"backward SR index vs scan verdict differ on: $name")
  }

  // --- forward general subsumption resolution: char-2 index vs scan retrieval (Phase 5, Step 4) A/B ---

  test("forward general subsumption resolution: the char-2 index and scan reach the same verdict (A/B)") {
    // Both forward-SR paths use the same char-2 helper (flip a literal of the new clause, find subsumers of the
    // flipped clause), differing only in retrieval — feature-vector index vs `active` scan — over the same
    // candidate set applied in id order, so the verdicts must match.
    def cat(r: Discount.Result): String = r match
      case _: Discount.Result.Refutation => "refuted"
      case Discount.Result.Saturated     => "saturated"
      case Discount.Result.Unknown       => "unknown"
    def verdict(indexed: Boolean, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, equality = false, subsumptionIndexing = indexed,
        forwardSubsumptionResolution = true, backwardSubsumptionResolution = true).saturate(cs, maxGiven = 5000))

    val builders: Seq[(String, Fix => Seq[Clause])] = Seq(
      "2-literal simplifier resolves the new clause, then refute" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val R = pred("R", 1); val a = const("a"); val b = const("b"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))),
            clause(pos(app(P, a)), pos(app(Q, a)), pos(app(R, b))),
            clause(neg(app(Q, a))), clause(neg(app(R, b)))) },
      "propositional 2-literal forward SR chain" -> { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(neg(p), pos(r)), clause(pos(p), pos(q)), clause(neg(q)), clause(neg(r))) },
      "no forward SR applies (paths are no-ops)" -> { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))), clause(pos(app(P, a))), clause(neg(app(Q, a)))) }
    )
    for (name, b) <- builders do
      assert(verdict(indexed = true, b) == verdict(indexed = false, b), s"forward SR index vs scan verdict differ on: $name")
  }
