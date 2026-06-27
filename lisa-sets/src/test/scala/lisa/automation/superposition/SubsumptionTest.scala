package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/** Tests for θ-subsumption ([[Subsumption.subsumes]] and the [[Subsumption.sigSubsumes]] pre-filter).
 *  Convention: the subsuming clause `c` is the pattern (its variables bind); `d` is the rigid target. */
class SubsumptionTest extends AnyFunSuite:

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
    def cl(lits: Literal*): Clause = bank.mkClause(lits.toArray)

    /** Does `c` subsume `d`? (subsumes restores the trail itself, on both paths.) */
    def sub(c: Clause, d: Clause): Boolean = Subsumption.subsumes(bank, trail, c, d)

    /** Unit deletion: the shrunk `main \ {K}` if `unit` resolves a literal away, else `None`. */
    def unitDel(unit: Clause, main: Clause): Option[Clause] = Subsumption.unitDeletionResolvent(bank, trail, unit, main)

  // --- units and identity ---------------------------------------------------------------------

  test("a clause subsumes itself (the substitution is the identity)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    assert(sub(cl(pos(app(p, a))), cl(pos(app(p, a)))))
    val c = cl(pos(app(p, v(0))), neg(app(q, v(0))))
    assert(sub(c, c))
  }

  test("a unit variable clause subsumes any clause containing an instance of it") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    assert(sub(cl(pos(app(p, v(0)))), cl(pos(app(p, a))))) //                P(x) ⊑ P(a)
    assert(sub(cl(pos(app(p, v(0)))), cl(pos(app(p, a)), pos(app(q, b))))) // P(x) ⊑ {P(a), Q(b)}
  }

  test("subsumption is directional: a ground unit is not subsumed by a more general one's converse") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    assert(sub(cl(pos(app(p, v(0)))), cl(pos(app(p, a))))) //  P(x) ⊑ P(a)
    assert(!sub(cl(pos(app(p, a))), cl(pos(app(p, v(0)))))) // P(a) ⋢ P(x): a cannot match the rigid var
  }

  test("a unit clause does not subsume a clause with a different predicate or polarity") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    assert(!sub(cl(pos(app(p, v(0)))), cl(pos(app(q, a))))) // different predicate (pre-filter)
    assert(!sub(cl(pos(app(p, v(0)))), cl(neg(app(p, a))))) // wrong polarity
  }

  // --- multi-literal, shared substitution -----------------------------------------------------

  test("a multi-literal clause subsumes with one shared substitution") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1)
    val a = const("a"); val b = const("b")
    // {P(x), Q(x)} ⊑ {P(a), Q(a), R(b)} via x ↦ a
    assert(sub(cl(pos(app(p, v(0))), pos(app(q, v(0)))), cl(pos(app(p, a)), pos(app(q, a)), pos(app(r, b)))))
  }

  test("a shared variable that cannot be consistent across literals blocks subsumption") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {P(x), Q(x)} ⋢ {P(a), Q(b)}: x would have to be both a and b
    assert(!sub(cl(pos(app(p, v(0))), pos(app(q, v(0)))), cl(pos(app(p, a)), pos(app(q, b)))))
  }

  test("subsumption requires consistency under function symbols (backtracking the assignment)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    // {P(x), P(f(x))} ⊑ {P(a), P(f(a))} via x ↦ a (the matcher may have to try both pairings)
    assert(sub(cl(pos(app(p, v(0))), pos(app(p, app(f, v(0))))), cl(pos(app(p, a)), pos(app(p, app(f, a))))))
    // {P(x), P(f(x))} ⋢ {P(a), P(f(b))}: no x makes both P(x)=P(a/ f(b)) and P(f(x)) line up
    assert(!sub(cl(pos(app(p, v(0))), pos(app(p, app(f, v(0))))), cl(pos(app(p, a)), pos(app(p, app(f, b))))))
  }

  test("mixed polarities are matched to like-polarity literals") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    // {P(x), ¬Q(x)} ⊑ {P(a), ¬Q(a)}
    assert(sub(cl(pos(app(p, v(0))), neg(app(q, v(0)))), cl(pos(app(p, a)), neg(app(q, a)))))
    // {P(x), ¬Q(x)} ⋢ {P(a), Q(a)}: the negative literal has no negative partner (negCount filter)
    assert(!sub(cl(pos(app(p, v(0))), neg(app(q, v(0)))), cl(pos(app(p, a)), pos(app(q, a)))))
  }

  // --- injectivity (the multiset condition) ---------------------------------------------------

  test("the literal map must be injective: two pattern literals cannot share one target") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 0); val a = const("a"); val c = const("c")
    // {P(x), P(y)} vs {P(a), Q}: sizes/counts pass the pre-filter, but both P-literals have only
    // the single target P(a) to map to -- injectivity forbids reusing it, so NOT subsumed.
    val cc = cl(pos(app(p, v(0))), pos(app(p, v(1))))
    val dd = cl(pos(app(p, a)), pos(bank.mkConst(q)))
    assert(!sub(cc, dd))
    // but against {P(a), P(c)} the two literals get distinct targets: x ↦ a, y ↦ c
    assert(sub(cc, cl(pos(app(p, a)), pos(app(p, c)))))
  }

  test("distinct pattern variables may still map to the same target term across literals") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a")
    // {P(x), Q(y)} ⊑ {P(a), Q(a)}: x ↦ a and y ↦ a is fine -- injectivity is over target *literals*,
    // not over the substitution.
    assert(sub(cl(pos(app(p, v(0))), pos(app(q, v(1)))), cl(pos(app(p, a)), pos(app(q, a)))))
  }

  // --- the empty clause -----------------------------------------------------------------------

  test("the empty clause subsumes everything; nothing nonempty subsumes the empty clause") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    val empty = cl()
    assert(sub(empty, cl(pos(app(p, a)))))
    assert(sub(empty, empty))
    assert(!sub(cl(pos(app(p, a))), empty)) // size pre-filter: 1 > 0
  }

  // --- the signature pre-filter ---------------------------------------------------------------

  test("the pre-filter rejects on size, polarity counts, weight and predicate fingerprint") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val pa = cl(pos(app(p, a)))
    // size: a 2-literal clause cannot subsume a 1-literal one
    assert(!Subsumption.sigSubsumes(cl(pos(app(p, a)), pos(app(q, b))), pa))
    // predicate fingerprint: Q's bit is not present in {P(a)}
    assert(!Subsumption.sigSubsumes(cl(pos(app(q, v(0)))), pa))
    // weight: P(f(x)) is heavier than P(a), so it cannot subsume it (and indeed cannot match)
    assert(!Subsumption.sigSubsumes(cl(pos(app(p, app(f, v(0))))), pa))
    assert(!sub(cl(pos(app(p, app(f, v(0))))), pa))
    // a genuine subsumption passes the pre-filter
    assert(Subsumption.sigSubsumes(cl(pos(app(p, v(0)))), pa))
  }

  // --- propositional / ground --------------------------------------------------------------

  test("propositional clauses subsume by literal-set inclusion") {
    val fx = new Fix; import fx.*
    val p = pred("P", 0); val q = pred("Q", 0); val r = pred("R", 0)
    val pp = pos(bank.mkConst(p)); val qq = pos(bank.mkConst(q)); val rr = pos(bank.mkConst(r))
    assert(sub(cl(pp, qq), cl(pp, qq, rr))) //  {P,Q} ⊑ {P,Q,R}
    assert(!sub(cl(pp, rr), cl(pp, qq))) //     {P,R} ⋢ {P,Q}: R has no partner
  }

  // --- trail hygiene --------------------------------------------------------------------------

  test("subsumes leaves the trail clean on both the true and false paths") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val before = trail.save()
    assert(sub(cl(pos(app(p, v(0)))), cl(pos(app(p, a))))) //                       success
    assert(trail.save() == before)
    assert(!sub(cl(pos(app(p, v(0))), pos(app(q, v(0)))), cl(pos(app(p, a)), pos(app(q, b))))) // failure mid-search
    assert(trail.save() == before)
  }

  // --- unit deletion (unit subsumption resolution) --------------------------------------------

  test("a negative unit deletes a matching positive literal, leaving the rest") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {¬P(x)} resolves P(a) out of {P(a), Q(b)} -> {Q(b)}
    val r = unitDel(cl(neg(app(p, v(0)))), cl(pos(app(p, a)), pos(app(q, b))))
    assert(r.isDefined && r.get.size == 1)
    assert(sub(r.get, cl(pos(app(q, b))))) //  the survivor is Q(b)...
    assert(!sub(r.get, cl(pos(app(p, a))))) // ...not P(a)
  }

  test("unit deletion requires opposite polarity (same polarity is subsumption, not deletion)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {P(x)} shares P(a)'s polarity, so there is nothing to resolve away (it *subsumes* instead)
    assert(unitDel(cl(pos(app(p, v(0)))), cl(pos(app(p, a)), pos(app(q, b)))).isEmpty)
  }

  test("unit deletion needs a one-sided match: a ground unit cannot delete a more general literal") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    // {¬P(a)} vs {P(x), Q(b)}: matching P(a) onto P(x) fails (x is rigid) -- deleting it would need to
    // bind x (a *generating* resolution), so it is not a unit deletion.
    assert(unitDel(cl(neg(app(p, a))), cl(pos(app(p, v(0))), pos(app(q, b)))).isEmpty)
  }

  test("a unit and a complementary unit delete to the empty clause (unit conflict)") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val a = const("a")
    // {P(x)} resolves ¬P(a) out of {¬P(a)} -> □ (x ↦ a)
    val r = unitDel(cl(pos(app(p, v(0)))), cl(neg(app(p, a))))
    assert(r.isDefined && r.get.isEmpty)
  }

  test("the pre-filter rejects a unit whose predicate or polarity cannot match") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1); val a = const("a"); val b = const("b")
    // different predicate: R(x) has no opposite-polarity R-literal in {P(a), Q(b)}
    assert(unitDel(cl(neg(app(r, v(0)))), cl(pos(app(p, a)), pos(app(q, b)))).isEmpty)
    // right predicate but wrong polarity: {¬P(x)} needs a positive P in an all-negative main
    assert(unitDel(cl(neg(app(p, v(0)))), cl(neg(app(p, a)), neg(app(q, b)))).isEmpty)
  }

  test("unit deletion matches under function symbols and removes exactly one literal") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val f = fn("f", 1); val g = fn("g", 1)
    val a = const("a"); val b = const("b")
    // {¬P(f(x))} deletes P(f(a)) from {P(f(a)), Q(b)} -> {Q(b)}
    val r = unitDel(cl(neg(app(p, app(f, v(0))))), cl(pos(app(p, app(f, a))), pos(app(q, b))))
    assert(r.isDefined && r.get.size == 1 && sub(r.get, cl(pos(app(q, b)))))
    // but a head mismatch (g vs f) does not match
    assert(unitDel(cl(neg(app(p, app(f, v(0))))), cl(pos(app(p, app(g, a))), pos(app(q, b)))).isEmpty)
  }

  test("unit deletion leaves the trail clean") {
    val fx = new Fix; import fx.*
    val p = pred("P", 1); val q = pred("Q", 1); val a = const("a"); val b = const("b")
    val before = trail.save()
    assert(unitDel(cl(neg(app(p, v(0)))), cl(pos(app(p, a)), pos(app(q, b)))).isDefined) // a hit
    assert(trail.save() == before)
    assert(unitDel(cl(neg(app(p, a))), cl(pos(app(p, v(0))), pos(app(q, b)))).isEmpty) //  a miss
    assert(trail.save() == before)
  }
