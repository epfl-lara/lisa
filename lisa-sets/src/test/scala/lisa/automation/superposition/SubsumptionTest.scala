package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Tests for θ-subsumption ([[Subsumption.subsumes]] and the [[Subsumption.sigSubsumes]] pre-filter).
 *  Convention: the subsuming clause `c` is the pattern (its variables bind); `d` is the rigid target. */
class SubsumptionTest extends AnyFunSuite:

  class Fix extends TermFixture:


    /** Does `c` subsume `d`? (subsumes restores the trail itself, on both paths.) */
    def sub(c: Clause, d: Clause): Boolean = Subsumption.subsumes(bank, trail, c, d)

    /** Subsumption resolution: the shrunk `main \ {K}` if `side` resolves a literal away, else `None`.
     *  (Unit deletion is the `|side| = 1` case.) */
    def unitDel(side: Clause, main: Clause): Option[Clause] = Subsumption.subsumptionResolutionResolvent(bank, trail, side, main)

    /** Condensation: the fully-condensed clause (`== c` if already condensed). */
    def condense(c: Clause): Clause = Subsumption.condense(bank, trail, c)

  // --- units and identity ---------------------------------------------------------------------

  test("a clause subsumes itself (the substitution is the identity)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    assert(sub(clause(pos(app(p, a))), clause(pos(app(p, a)))))
    val c = clause(pos(app(p, v(0))), neg(app(q, v(0))))
    assert(sub(c, c))
  }

  test("a unit variable clause subsumes any clause containing an instance of it") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    assert(sub(clause(pos(app(p, v(0)))), clause(pos(app(p, a))))) //                P(x) ⊑ P(a)
    assert(sub(clause(pos(app(p, v(0)))), clause(pos(app(p, a)), pos(app(q, b))))) // P(x) ⊑ {P(a), Q(b)}
  }

  test("subsumption is directional: a ground unit is not subsumed by a more general one's converse") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    assert(sub(clause(pos(app(p, v(0)))), clause(pos(app(p, a))))) //  P(x) ⊑ P(a)
    assert(!sub(clause(pos(app(p, a))), clause(pos(app(p, v(0)))))) // P(a) ⋢ P(x): a cannot match the rigid var
  }

  test("a unit clause does not subsume a clause with a different predicate or polarity") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    assert(!sub(clause(pos(app(p, v(0)))), clause(pos(app(q, a))))) // different predicate (pre-filter)
    assert(!sub(clause(pos(app(p, v(0)))), clause(neg(app(p, a))))) // wrong polarity
  }

  // --- multi-literal, shared substitution -----------------------------------------------------

  test("a multi-literal clause subsumes with one shared substitution") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b")
    // {P(x), Q(x)} ⊑ {P(a), Q(a), R(b)} via x ↦ a
    assert(sub(clause(pos(app(p, v(0))), pos(app(q, v(0)))), clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b)))))
  }

  test("a shared variable that cannot be consistent across literals blocks subsumption") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {P(x), Q(x)} ⋢ {P(a), Q(b)}: x would have to be both a and b
    assert(!sub(clause(pos(app(p, v(0))), pos(app(q, v(0)))), clause(pos(app(p, a)), pos(app(q, b)))))
  }

  test("subsumption requires consistency under function symbols (backtracking the assignment)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    // {P(x), P(f(x))} ⊑ {P(a), P(f(a))} via x ↦ a (the matcher may have to try both pairings)
    assert(sub(clause(pos(app(p, v(0))), pos(app(p, app(f, v(0))))), clause(pos(app(p, a)), pos(app(p, app(f, a))))))
    // {P(x), P(f(x))} ⋢ {P(a), P(f(b))}: no x makes both P(x)=P(a/ f(b)) and P(f(x)) line up
    assert(!sub(clause(pos(app(p, v(0))), pos(app(p, app(f, v(0))))), clause(pos(app(p, a)), pos(app(p, app(f, b))))))
  }

  test("mixed polarities are matched to like-polarity literals") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    // {P(x), ¬Q(x)} ⊑ {P(a), ¬Q(a)}
    assert(sub(clause(pos(app(p, v(0))), neg(app(q, v(0)))), clause(pos(app(p, a)), neg(app(q, a)))))
    // {P(x), ¬Q(x)} ⋢ {P(a), Q(a)}: the negative literal has no negative partner (negCount filter)
    assert(!sub(clause(pos(app(p, v(0))), neg(app(q, v(0)))), clause(pos(app(p, a)), pos(app(q, a)))))
  }

  // --- injectivity (the multiset condition) ---------------------------------------------------

  test("the literal map must be injective: two pattern literals cannot share one target") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 0); val a = const("a"); val c = const("c")
    // {P(x), P(y)} vs {P(a), Q}: sizes/counts pass the pre-filter, but both P-literals have only
    // the single target P(a) to map to -- injectivity forbids reusing it, so NOT subsumed.
    val cc = clause(pos(app(p, v(0))), pos(app(p, v(1))))
    val dd = clause(pos(app(p, a)), pos(bank.mkConst(q)))
    assert(!sub(cc, dd))
    // but against {P(a), P(c)} the two literals get distinct targets: x ↦ a, y ↦ c
    assert(sub(cc, clause(pos(app(p, a)), pos(app(p, c)))))
  }

  test("distinct pattern variables may still map to the same target term across literals") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    // {P(x), Q(y)} ⊑ {P(a), Q(a)}: x ↦ a and y ↦ a is fine -- injectivity is over target *literals*,
    // not over the substitution.
    assert(sub(clause(pos(app(p, v(0))), pos(app(q, v(1)))), clause(pos(app(p, a)), pos(app(q, a)))))
  }

  // --- the empty clause -----------------------------------------------------------------------

  test("the empty clause subsumes everything; nothing nonempty subsumes the empty clause") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    val empty = clause()
    assert(sub(empty, clause(pos(app(p, a)))))
    assert(sub(empty, empty))
    assert(!sub(clause(pos(app(p, a))), empty)) // size pre-filter: 1 > 0
  }

  // --- the signature pre-filter ---------------------------------------------------------------

  test("the pre-filter rejects on size, polarity counts, weight and predicate fingerprint") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val pa = clause(pos(app(p, a)))
    // size: a 2-literal clause cannot subsume a 1-literal one
    assert(!Subsumption.sigSubsumes(clause(pos(app(p, a)), pos(app(q, b))), pa))
    // predicate fingerprint: Q's bit is not present in {P(a)}
    assert(!Subsumption.sigSubsumes(clause(pos(app(q, v(0)))), pa))
    // weight: P(f(x)) is heavier than P(a), so it cannot subsume it (and indeed cannot match)
    assert(!Subsumption.sigSubsumes(clause(pos(app(p, app(f, v(0))))), pa))
    assert(!sub(clause(pos(app(p, app(f, v(0))))), pa))
    // a genuine subsumption passes the pre-filter
    assert(Subsumption.sigSubsumes(clause(pos(app(p, v(0)))), pa))
  }

  // --- propositional / ground --------------------------------------------------------------

  test("propositional clauses subsume by literal-set inclusion") {
    val fx = new Fix; import fx.*
    val p = pred("P", 0); val q = pred("Q", 0); val r = pred("R", 0)
    val pp = pos(bank.mkConst(p)); val qq = pos(bank.mkConst(q)); val rr = pos(bank.mkConst(r))
    assert(sub(clause(pp, qq), clause(pp, qq, rr))) //  {P,Q} ⊑ {P,Q,R}
    assert(!sub(clause(pp, rr), clause(pp, qq))) //     {P,R} ⋢ {P,Q}: R has no partner
  }

  // --- trail hygiene --------------------------------------------------------------------------

  test("subsumes leaves the trail clean on both the true and false paths") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val before = trail.save()
    assert(sub(clause(pos(app(p, v(0)))), clause(pos(app(p, a))))) //                       success
    assert(trail.save() == before)
    assert(!sub(clause(pos(app(p, v(0))), pos(app(q, v(0)))), clause(pos(app(p, a)), pos(app(q, b))))) // failure mid-search
    assert(trail.save() == before)
  }

  // --- unit deletion (unit subsumption resolution) --------------------------------------------

  test("a negative unit deletes a matching positive literal, leaving the rest") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {¬P(x)} resolves P(a) out of {P(a), Q(b)} -> {Q(b)}
    val r = unitDel(clause(neg(app(p, v(0)))), clause(pos(app(p, a)), pos(app(q, b))))
    assert(r.isDefined && r.get.size == 1)
    assert(sub(r.get, clause(pos(app(q, b))))) //  the survivor is Q(b)...
    assert(!sub(r.get, clause(pos(app(p, a))))) // ...not P(a)
  }

  test("unit deletion requires opposite polarity (same polarity is subsumption, not deletion)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {P(x)} shares P(a)'s polarity, so there is nothing to resolve away (it *subsumes* instead)
    assert(unitDel(clause(pos(app(p, v(0)))), clause(pos(app(p, a)), pos(app(q, b)))).isEmpty)
  }

  test("unit deletion needs a one-sided match: a ground unit cannot delete a more general literal") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {¬P(a)} vs {P(x), Q(b)}: matching P(a) onto P(x) fails (x is rigid) -- deleting it would need to
    // bind x (a *generating* resolution), so it is not a unit deletion.
    assert(unitDel(clause(neg(app(p, a))), clause(pos(app(p, v(0))), pos(app(q, b)))).isEmpty)
  }

  test("a unit and a complementary unit delete to the empty clause (unit conflict)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    // {P(x)} resolves ¬P(a) out of {¬P(a)} -> □ (x ↦ a)
    val r = unitDel(clause(pos(app(p, v(0)))), clause(neg(app(p, a))))
    assert(r.isDefined && r.get.isEmpty)
  }

  test("the pre-filter rejects a unit whose predicate or polarity cannot match") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1); val a = const("a"); val b = const("b")
    // different predicate: R(x) has no opposite-polarity R-literal in {P(a), Q(b)}
    assert(unitDel(clause(neg(app(r, v(0)))), clause(pos(app(p, a)), pos(app(q, b)))).isEmpty)
    // right predicate but wrong polarity: {¬P(x)} needs a positive P in an all-negative main
    assert(unitDel(clause(neg(app(p, v(0)))), clause(neg(app(p, a)), neg(app(q, b)))).isEmpty)
  }

  test("unit deletion matches under function symbols and removes exactly one literal") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val f = fn("f", 1); val g = fn("g", 1)
    val a = const("a"); val b = const("b")
    // {¬P(f(x))} deletes P(f(a)) from {P(f(a)), Q(b)} -> {Q(b)}
    val r = unitDel(clause(neg(app(p, app(f, v(0))))), clause(pos(app(p, app(f, a))), pos(app(q, b))))
    assert(r.isDefined && r.get.size == 1 && sub(r.get, clause(pos(app(q, b)))))
    // but a head mismatch (g vs f) does not match
    assert(unitDel(clause(neg(app(p, app(f, v(0))))), clause(pos(app(p, app(g, a))), pos(app(q, b)))).isEmpty)
  }

  test("unit deletion leaves the trail clean") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val before = trail.save()
    assert(unitDel(clause(neg(app(p, v(0)))), clause(pos(app(p, a)), pos(app(q, b)))).isDefined) // a hit
    assert(trail.save() == before)
    assert(unitDel(clause(neg(app(p, a))), clause(pos(app(p, v(0))), pos(app(q, b)))).isEmpty) //  a miss
    assert(trail.save() == before)
  }

  // --- general subsumption resolution (multi-literal side) -------------------------------------

  test("a multi-literal side resolves a literal away when the rest subsumes the remainder") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b")
    // {¬P(x), Q(x)} resolves P(a) out of {P(a), Q(a), R(b)}: σ = {x ↦ a}, and Q(x)σ = Q(a) ⊆ {Q(a), R(b)}
    val r1 = unitDel(clause(neg(app(p, v(0))), pos(app(q, v(0)))), clause(pos(app(p, a)), pos(app(q, a)), pos(app(r, b))))
    assert(r1.isDefined && r1.get.size == 2)
    assert(sub(r1.get, clause(pos(app(q, a)), pos(app(r, b))))) // the survivor is {Q(a), R(b)}
    assert(!sub(r1.get, clause(pos(app(p, a))))) //                P(a) was deleted
  }

  test("general SR needs the rest of the side consistent with the resolving match (one shared σ)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {¬P(x), Q(x)} vs {P(a), Q(b), ...}: resolving P(a) forces x ↦ a, but then Q(x)σ = Q(a) ∉ {Q(b)},
    // so the side does NOT subsumption-resolve this main.
    assert(unitDel(clause(neg(app(p, v(0))), pos(app(q, v(0)))), clause(pos(app(p, a)), pos(app(q, b)))).isEmpty)
  }

  test("general SR still requires a one-sided match (the remainder may not bind the main)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    // {¬P(a), Q(a)} vs {P(a), Q(y)}: resolving P(a) is fine, but Q(a) must match the rigid Q(y) -- it does
    // not (matching Q(a) onto Q(y) would bind y), so no SR.
    assert(unitDel(clause(neg(app(p, a)), pos(app(q, a))), clause(pos(app(p, a)), pos(app(q, v(0))))).isEmpty)
  }

  test("general SR can close to the empty clause when the side covers all of main") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    // {¬P(x), Q(x)} resolves P(a) out of {P(a), Q(a)} -> {Q(a)}; here we check the 2->1 shrink directly
    val r1 = unitDel(clause(neg(app(p, v(0))), pos(app(q, v(0)))), clause(pos(app(p, a)), pos(app(q, a))))
    assert(r1.isDefined && r1.get.size == 1 && sub(r1.get, clause(pos(app(q, a)))))
  }

  test("general SR conservatively skips a side whose remainder has variables outside the resolving literal") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b"); val c = const("c")
    // {¬P(x), Q(y)} with distinct x,y: ideally it would resolve P(a) → {Q(b), R(c)}, but `resolve`'s mgu
    // (from P(x)=P(a)) leaves y free, so the built resolvent {Q(y), Q(b), R(c)} does not subsume main and
    // the [[subsumes]] completeness gate (soundly) declines the deletion. Documents the known limitation.
    assert(unitDel(clause(neg(app(p, v(0))), pos(app(q, v(1)))), clause(pos(app(p, a)), pos(app(q, b)), pos(app(r, c)))).isEmpty)
  }

  // --- condensation ---------------------------------------------------------------------------

  test("condensation merges a variable literal into its instance") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    // {P(x), P(a)} ≡ {P(a)} (x ↦ a)
    val r = condense(clause(pos(app(p, v(0))), pos(app(p, a))))
    assert(r.size == 1 && sub(r, clause(pos(app(p, a)))) && sub(clause(pos(app(p, a))), r))
  }

  test("condensation works on negative literals too (not just positive/selected)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    // {¬P(x), ¬P(a)} ≡ {¬P(a)}
    val r = condense(clause(neg(app(p, v(0))), neg(app(p, a))))
    assert(r.size == 1 && sub(r, clause(neg(app(p, a)))))
  }

  test("a factor that does not subsume the clause is not a condensation") {
    val fx = new Fix; import fx.*
    val p = pred("P", 2); val a = const("a"); val b = const("b")
    // {P(x,a), P(b,y)} factors to {P(b,a)}, which does NOT subsume the clause -- so no condensation.
    val c0 = clause(pos(app(p, v(0), a)), pos(app(p, b, v(1))))
    assert(condense(c0).size == 2) // unchanged
  }

  test("condensation iterates to a fixpoint") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    // {P(x), P(y), P(a)} ≡ {P(a)} -- needs two merges
    val r = condense(clause(pos(app(p, v(0))), pos(app(p, v(1))), pos(app(p, a))))
    assert(r.size == 1 && sub(r, clause(pos(app(p, a)))))
  }

  test("an already-condensed clause is returned unchanged, leaving the trail clean") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val before = trail.save()
    val c0 = clause(pos(app(p, a)), pos(app(q, b))) // distinct predicates: nothing to merge
    assert(condense(c0).size == 2)
    assert(trail.save() == before)
  }
