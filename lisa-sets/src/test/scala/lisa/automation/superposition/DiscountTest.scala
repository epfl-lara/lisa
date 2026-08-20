package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*
import lisa.automation.superposition.ordering.*

/** Tests for the DISCOUNT saturation loop ([[Discount]]). */
class DiscountTest extends AnyFunSuite:

  class Fix extends TermFixture:

    /** A loop over `cs`. One `Discount` saturates one clause set, so this takes it: there is no reset. */
    def discount(cs: Seq[Clause], opts: SearchOptions = SearchOptions()): Discount = new Discount(bank, trail, cs, opts)

  /** The saturation verdict as a string, so the tables of expected outcomes below read directly. */
  private def cat(r: Discount.Result): String = r match
    case _: Discount.Result.Refutation => "refuted"
    case Discount.Result.Saturated     => "saturated"
    case Discount.Result.Unknown       => "unknown"

  test("propositional P and ¬P refute") {
    val fx = new Fix; import fx.*
    val p = prop("P")
    val r = discount(Seq(clause(pos(p)), clause(neg(p)))).saturate()
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
    assert(discount(cs).saturate().isInstanceOf[Discount.Result.Refutation])
  }

  test("first-order resolution with unification refutes") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(q, x))), // ¬P(x) ∨ Q(x)
      clause(pos(app(p, a))), //                 P(a)
      clause(neg(app(q, a))) //                  ¬Q(a)
    )
    assert(discount(cs).saturate().isInstanceOf[Discount.Result.Refutation])
  }

  test("a satisfiable set saturates") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val r = discount(Seq(clause(pos(app(p, a))), clause(pos(app(q, b))))).saturate()
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
    assert(discount(cs, SearchOptions(maxGiven = 5)).saturate() == Discount.Result.Unknown)
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
    assert(discount(cs).saturate().isInstanceOf[Discount.Result.Refutation])
  }

  test("complete selector refutes a factoring problem (selects all maximal positives)") {
    val fx = new Fix; import fx.*
    bank.selector = new CompleteBestLiteralSelector(bank.order)
    val p = pred("P", 1); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
    val cs = Seq(
      clause(pos(app(p, x)), pos(app(p, y))), //  P(x) ∨ P(y) -- both maximal, both selected
      clause(neg(app(p, a)), neg(app(p, b))) //  ¬P(a) ∨ ¬P(b)
    )
    assert(discount(cs).saturate().isInstanceOf[Discount.Result.Refutation])
  }

  test("the factoring after-check still refutes the factoring problem") {
    val fx = new Fix; import fx.*
    bank.selector = new CompleteBestLiteralSelector(bank.order)
    val p = pred("P", 1); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
    val cs = Seq(clause(pos(app(p, x)), pos(app(p, y))), clause(neg(app(p, a)), neg(app(p, b))))
    val d = new Discount(bank, trail, cs, SearchOptions(factorAfterCheck = true))
    assert(d.saturate().isInstanceOf[Discount.Result.Refutation])
  }

  test("the refutation's empty clause traces back to the input clauses") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(q, x))),
      clause(pos(app(p, a))),
      clause(neg(app(q, a)))
    )
    discount(cs).saturate() match
      case Discount.Result.Refutation(empty) =>
        def inputLeaves(c: Clause): Int =
          if c.justification == Justification.Input then 1 else c.justification.premises.map(inputLeaves).sum
        assert(empty.isEmpty)
        assert(inputLeaves(empty) >= 2) // derived from at least two input clauses
      case other => fail(s"expected Refutation, got $other")
  }

  // --- subsumption ------------------------------------------------------------------------------

  test("backward subsumption deletes an active clause subsumed by the given") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    // {P(a)} is selected first (equal weight, smaller id), then the more general {P(x)} subsumes it.
    val d = new Discount(bank, trail, Seq(clause(pos(app(p, a))), clause(pos(app(p, x)))))
    val r = d.saturate()
    assert(r == Discount.Result.Saturated)
    assert(d.stats.backwardSubsumed == 1) // {P(x)} backward-subsumes the already-active {P(a)}
    assert(d.stats.forwardSubsumed == 0) // {P(a)} does not subsume {P(x)} (a cannot match the rigid x)
  }

  test("forward subsumption skips a subsumed clause at selection") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // {P(x)} (lighter) is activated first; the heavier {P(a), Q(b)} is then subsumed on selection.
    val d = new Discount(bank, trail, Seq(clause(pos(app(p, x))), clause(pos(app(p, a)), pos(app(q, b)))))
    val r = d.saturate()
    assert(r == Discount.Result.Saturated)
    assert(d.stats.forwardSubsumed == 1) // {P(a), Q(b)} subsumed by the active {P(x)}
    assert(d.stats.backwardSubsumed == 0)
  }

  test("forward subsumption discards a generated clause (addPassive path)") {
    val fx = new Fix; import fx.*
    bank.selector = FirstNegativeSelector // all-positive clauses resolve on their first (canonical) literal
    // `a` is interned first, so it has the smallest symbol code and sorts first under canonicalisation --
    // ensuring the all-positive {a,c} keeps `a` as its selected literal so resolution on a/¬a fires.
    val a = prop("a"); val b = prop("b"); val c = prop("c")
    // {b,c} is activated first; resolving {¬a,b} and {a,c} regenerates {b,c}, which the active {b,c} subsumes.
    // Force forward simplify at generation on (it is off by default) so this exercises the addPassive path.
    val d = new Discount(bank, trail, Seq(clause(pos(b), pos(c)), clause(neg(a), pos(b)), clause(pos(a), pos(c))), SearchOptions(forwardSimplifyAtGeneration = true))
    val r = d.saturate()
    assert(r == Discount.Result.Saturated)
    assert(d.stats.forwardSubsumed >= 1) // the resolvent {b,c} is subsumed by the active {b,c} at addPassive
    assert(d.stats.backwardSubsumed == 0)
  }

  test("with both flags off, subsumption is inert (pure simplification)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    // same inputs as the backward-subsumption test, but no simplification: same verdict, no deletions.
    val d = new Discount(bank, trail, Seq(clause(pos(app(p, a))), clause(pos(app(p, x)))), SearchOptions(forwardSubsumption = false, backwardSubsumption = false))
    val r = d.saturate()
    assert(r == Discount.Result.Saturated)
    assert(d.stats.forwardSubsumed == 0 && d.stats.backwardSubsumed == 0)
  }

  test("subsumption preserves a refutation verdict (flags on and off agree)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
    val cs = Seq(
      clause(neg(app(p, x)), pos(app(q, x))), // ¬P(x) ∨ Q(x)
      clause(pos(app(p, a))), //                 P(a)
      clause(neg(app(q, a))) //                  ¬Q(a)
    )
    val on = new Discount(bank, trail, cs, SearchOptions(forwardSubsumption = true, backwardSubsumption = true))
    val off = new Discount(bank, trail, cs, SearchOptions(forwardSubsumption = false, backwardSubsumption = false))
    assert(on.saturate().isInstanceOf[Discount.Result.Refutation])
    assert(off.saturate().isInstanceOf[Discount.Result.Refutation])
  }

  // --- unit deletion ----------------------------------------------------------------------------

  test("forward unit deletion shrinks the given at selection") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // {¬P(x)} (lighter) activates first; selecting {P(a), Q(b)} then unit-deletes P(a) -> {Q(b)}.
    val d = new Discount(bank, trail, Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x)))))
    val r = d.saturate()
    assert(r == Discount.Result.Saturated)
    assert(d.stats.forwardUnitDeleted == 1)
    assert(d.stats.backwardUnitDeleted == 0)
  }

  test("backward unit deletion shrinks an active clause") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // Force age (FIFO) selection so {P(a), Q(b)} activates before the lighter unit {¬P(x)}; the unit then
    // backward-unit-deletes P(a) out of the active clause.
    val d = new Discount(bank, trail, Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x)))), SearchOptions(ageRatio = 1, weightRatio = 0))
    val r = d.saturate()
    assert(r == Discount.Result.Saturated)
    assert(d.stats.backwardUnitDeleted == 1)
    assert(d.stats.forwardUnitDeleted == 0)
  }

  test("a unit conflict via unit deletion closes the clause to □ (refutation)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    // {¬P(x)} deletes P(a) -> {Q(b)}; {¬Q(b)} then deletes Q(b) -> □.
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x))), clause(neg(app(q, b))))
    assert(new Discount(bank, trail, cs).saturate().isInstanceOf[Discount.Result.Refutation])
  }

  test("with unit-deletion flags off it is inert (pure simplification)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x))))
    val d = new Discount(bank, trail, cs, SearchOptions(forwardUnitDeletion = false, backwardUnitDeletion = false))
    assert(d.saturate() == Discount.Result.Saturated)
    assert(d.stats.forwardUnitDeleted == 0 && d.stats.backwardUnitDeleted == 0)
  }

  test("unit deletion preserves a refutation verdict (flags on and off agree)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, b))), clause(neg(app(p, x))), clause(neg(app(q, b))))
    val on = new Discount(bank, trail, cs, SearchOptions(forwardUnitDeletion = true, backwardUnitDeletion = true))
    val off = new Discount(bank, trail, cs, SearchOptions(forwardUnitDeletion = false, backwardUnitDeletion = false))
    assert(on.saturate().isInstanceOf[Discount.Result.Refutation])
    assert(off.saturate().isInstanceOf[Discount.Result.Refutation])
  }

  // --- general subsumption resolution (off by default; enabled explicitly here) ----------------

  test("forward general subsumption resolution shrinks the given at selection") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    // {¬P(x), Q(x)} (lighter) activates first; selecting {P(a), Q(a), R(b)} then SR-resolves P(a) → {Q(a), R(b)}.
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b))), clause(neg(app(p, x)), pos(app(q, x))))
    val d = new Discount(bank, trail, cs, SearchOptions(forwardSubsumptionResolution = true))
    assert(d.saturate() == Discount.Result.Saturated)
    assert(d.stats.forwardSubsumptionResolved == 1)
    assert(d.stats.backwardSubsumptionResolved == 0)
  }

  test("backward general subsumption resolution shrinks an active clause") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    // Force age order so {P(a), Q(a), R(b)} activates before the (multi-literal) side {¬P(x), Q(x)}.
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b))), clause(neg(app(p, x)), pos(app(q, x))))
    val d = new Discount(bank, trail, cs, SearchOptions(ageRatio = 1, weightRatio = 0, backwardSubsumptionResolution = true))
    assert(d.saturate() == Discount.Result.Saturated)
    assert(d.stats.backwardSubsumptionResolved == 1)
    assert(d.stats.forwardSubsumptionResolved == 0)
  }

  // General SR is ON by default; [[SearchOptions.forwardSubsumptionResolution]] records the ablation it was
  // chosen from. This test pins the default itself, so it fails if that flips without the doc following.
  test("general subsumption resolution is on by default, and inert when explicitly disabled") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b"); val x = v(0)
    val cs = Seq(clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b))), clause(neg(app(p, x)), pos(app(q, x))))
    val on = new Discount(bank, trail, cs) // SR flags now default true
    assert(on.saturate() == Discount.Result.Saturated)
    assert(on.stats.forwardSubsumptionResolved + on.stats.backwardSubsumptionResolved > 0, "SR should fire by default")
    val off = new Discount(bank, trail, cs, SearchOptions(forwardSubsumptionResolution = false, backwardSubsumptionResolution = false))
    assert(off.saturate() == Discount.Result.Saturated)
    assert(off.stats.forwardSubsumptionResolved == 0 && off.stats.backwardSubsumptionResolved == 0)
  }

  // --- condensation (off by default; enabled explicitly here) -----------------------------------

  test("condensation shrinks a clause at creation") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    // {P(x), P(a)} condenses to {P(a)} when it enters passive
    val d = new Discount(bank, trail, Seq(clause(pos(app(p, x)), pos(app(p, a)))), SearchOptions(condensation = true))
    assert(d.saturate() == Discount.Result.Saturated)
    assert(d.stats.condensed == 1)
  }

  test("condensation is off by default and inert when disabled") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    val d = new Discount(bank, trail, Seq(clause(pos(app(p, x)), pos(app(p, a))))) // condensation defaults false
    assert(d.saturate() == Discount.Result.Saturated)
    assert(d.stats.condensed == 0)
  }

  test("condensation preserves a refutation verdict (flags on and off agree)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a"); val x = v(0)
    val cs = Seq(clause(pos(app(p, x)), pos(app(p, a))), clause(neg(app(p, a))))
    val on = new Discount(bank, trail, cs, SearchOptions(condensation = true))
    val off = new Discount(bank, trail, cs, SearchOptions(condensation = false))
    assert(on.saturate().isInstanceOf[Discount.Result.Refutation])
    assert(off.saturate().isInstanceOf[Discount.Result.Refutation])
  }

  // --- resolution over the literal indices ------------------------------------------------------

  test("indexed resolution reaches the expected verdict on each shape of resolution problem") {
    // Was an A/B comparison against a linear active-set scan, which no longer exists; the verdicts are pinned
    // instead, so the same clause sets still pin the behaviour of the surviving path. The literal indices only
    // narrow the candidate set and every candidate is confirmed by `Inference.resolve`'s real unification, so
    // these verdicts are the calculus's. Equality is off throughout, so only resolution is exercised.
    def verdict(build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, cs, SearchOptions(equality = false, maxGiven = 5000)).saturate())

    val cases: Seq[(String, String, Fix => Seq[Clause])] = Seq(
      ("propositional P, ¬P", "refuted", { fx => import fx.*; val p = prop("P"); Seq(clause(pos(p)), clause(neg(p))) }),
      ("propositional chain ¬P∨Q, ¬Q∨R, P, ¬R", "refuted", { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(neg(p), pos(q)), clause(neg(q), pos(r)), clause(pos(p)), clause(neg(r))) }),
      ("first-order ¬P(x)∨Q(x), P(a), ¬Q(a)", "refuted", { fx => import fx.*
        val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(p, x)), pos(app(q, x))), clause(pos(app(p, a))), clause(neg(app(q, a)))) }),
      ("multi-predicate mix ¬P(x)∨¬Q(x)∨R(x), P(a), Q(a), ¬R(a)", "refuted", { fx => import fx.*
        val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(p, x)), neg(app(q, x)), pos(app(r, x))),
            clause(pos(app(p, a))), clause(pos(app(q, a))), clause(neg(app(r, a)))) }),
      // Needs the factor `{P(y)}`, so it needs *both* positives selected. That is what the complete selection
      // does on an all-positive clause, and it is the bank's default; under a one-literal selection such as
      // `BestLiteralSelector` the factoring step pairs nothing and this set saturates instead.
      ("needs factoring P(x)∨P(y), ¬P(a)∨¬P(b)", "refuted", { fx => import fx.*
        val p = pred("P", 1); val a = const("a"); val b = const("b"); val x = v(0); val y = v(1)
        Seq(clause(pos(app(p, x)), pos(app(p, y))), clause(neg(app(p, a)), neg(app(p, b)))) }),
      ("self-resolvable ¬P(x)∨P(f(x)), P(a), ¬P(f(f(a)))", "refuted", { fx => import fx.*
        val p = pred("P", 1); val f = fn("f", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(p, x)), pos(app(p, app(f, x)))), clause(pos(app(p, a))), clause(neg(app(p, app(f, app(f, a)))))) }),
      ("satisfiable P(a), Q(b)", "saturated", { fx => import fx.*
        val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
        Seq(clause(pos(app(p, a))), clause(pos(app(q, b)))) })
    )
    for (name, expected, b) <- cases do
      assert(verdict(b) == expected, s"expected $expected on: $name")
  }

  // --- simplification over the feature-vector index ---------------------------------------------

  test("indexed simplification reaches the expected verdict on each shape of redundancy") {
    // Was an A/B comparison against a linear active-set scan, which no longer exists; the verdicts are pinned
    // instead. The feature-vector index is a superset filter over the real `Subsumption.subsumes` and its
    // features are subsumption-monotone, so nothing that genuinely subsumes is outside the cone it descends.
    def verdict(build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, cs, SearchOptions(equality = false, maxGiven = 5000)).saturate())

    val cases: Seq[(String, String, Fix => Seq[Clause])] = Seq(
      ("unit subsumes a longer clause, then refute", "refuted", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val b = const("b"); val c = const("c"); val x = v(0)
        Seq(clause(pos(app(P, x))), clause(pos(app(P, a)), pos(app(Q, b))), clause(neg(app(P, c)))) }),
      ("satisfiable with redundant instances (forward subsumption)", "saturated", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val b = const("b"); val x = v(0)
        Seq(clause(pos(app(P, x))), clause(pos(app(P, a))), clause(pos(app(Q, b)))) }),
      ("first-order resolution refutation", "refuted", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))), clause(pos(app(P, a))), clause(neg(app(Q, a)))) }),
      ("propositional chain", "refuted", { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(neg(p), pos(q)), clause(neg(q), pos(r)), clause(pos(p)), clause(neg(r))) }),
      ("backward subsumption (general activates after instance), then refute", "refuted", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val d = const("d"); val x = v(0)
        Seq(clause(pos(app(P, a)), pos(app(Q, a))), clause(pos(app(P, x))), clause(neg(app(P, d)))) }),
      ("unit deletion shrinks then closes", "refuted", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a")
        Seq(clause(pos(app(P, a))), clause(neg(app(P, a)), pos(app(Q, a))), clause(neg(app(Q, a)))) })
    )
    for (name, expected, b) <- cases do
      assert(verdict(b) == expected, s"expected $expected on: $name")
  }

  // --- forward unit deletion: {¬K} index dispatch vs the activeUnits scan, A/B -------------------

  test("forward unit deletion: the {¬K} index dispatch and the activeUnits scan reach the same verdict (A/B)") {
    // Both forward-unit-deletion paths delete the same literals (complete candidate sets verified by the same
    // `subsumptionResolutionResolvent`), so forcing the index dispatch (threshold 0) vs the unit-sublist scan
    // (threshold ∞) must reach the same verdict. This is the one indexed-vs-scan A/B the engine still has: both
    // paths are live, since the threshold picks between them per call.
    def verdict(threshold: Int, build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, cs, SearchOptions(equality = false,
        forwardUnitDeletionIndexThreshold = threshold, maxGiven = 5000)).saturate())

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

  // --- general subsumption resolution, both directions, over the sign-flip index -----------------

  test("general subsumption resolution reaches the expected verdict in both directions") {
    // Was two A/B comparisons against a linear active-set scan, which no longer exists; the verdicts are pinned
    // instead, over the union of both tests' clause sets. Both directions flip each literal of the clause in
    // hand and query the feature-vector index with it (`foreachFlipped`): a stored clause SR-resolves on `Lᵢ`
    // exactly when it subsumes the clause with `Lᵢ` flipped, so the union of the flipped clauses' cones is a
    // complete superset of the victims, and each is verified by `subsumptionResolutionResolvent`.
    def verdict(build: Fix => Seq[Clause]): String =
      val fx = new Fix
      val cs = build(fx)
      cat(new Discount(fx.bank, fx.trail, cs, SearchOptions(equality = false,
        backwardSubsumptionResolution = true, forwardSubsumptionResolution = true, maxGiven = 5000)).saturate())

    val cases: Seq[(String, String, Fix => Seq[Clause])] = Seq(
      // backward: the simplifier arrives after its victim, so `gc` resolves an already-active clause
      ("backward: 2-literal clause SR-resolves a literal of an active clause, then refute", "refuted", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val R = pred("R", 1); val a = const("a"); val b = const("b"); val x = v(0)
        // {¬P(x), Q(x)} SR-resolves {P(a), Q(a), R(b)} on P(a) (rest {Q(x)}→{Q(a)} ⊆ target), deleting P(a).
        Seq(clause(pos(app(P, a)), pos(app(Q, a)), pos(app(R, b))),
            clause(neg(app(P, x)), pos(app(Q, x))),
            clause(neg(app(Q, a))), clause(neg(app(R, b)))) }),
      ("backward: propositional 2-literal SR chain", "refuted", { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(pos(p), pos(q)), clause(neg(p), pos(r)), clause(neg(q)), clause(neg(r))) }),
      // forward: the simplifier is already active when its victim is selected
      ("forward: 2-literal simplifier resolves the new clause, then refute", "refuted", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val R = pred("R", 1); val a = const("a"); val b = const("b"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))),
            clause(pos(app(P, a)), pos(app(Q, a)), pos(app(R, b))),
            clause(neg(app(Q, a))), clause(neg(app(R, b)))) }),
      ("forward: propositional 2-literal SR chain", "refuted", { fx => import fx.*
        val p = prop("P"); val q = prop("Q"); val r = prop("R")
        Seq(clause(neg(p), pos(r)), clause(pos(p), pos(q)), clause(neg(q)), clause(neg(r))) }),
      ("no SR applies at all (both directions are no-ops)", "refuted", { fx => import fx.*
        val P = pred("P", 1); val Q = pred("Q", 1); val a = const("a"); val x = v(0)
        Seq(clause(neg(app(P, x)), pos(app(Q, x))), clause(pos(app(P, a))), clause(neg(app(Q, a)))) })
    )
    for (name, expected, b) <- cases do
      assert(verdict(b) == expected, s"expected $expected on: $name")
  }
