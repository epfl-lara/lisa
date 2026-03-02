package lisa.maths.SetTheory

/**
 * Test cases for Congruence used with premises (thenHave ... by Congruence).
 * Uses only uninterpreted symbols — no set theory.
 *
 * The current bug: when Congruence.from cuts in a premise, it leaks the
 * premise's LHS formulas into the result. For example, going from
 *   p(x) ⊢ p(x)
 * to
 *   (p(y), x === y) ⊢ p(x)
 * actually produces
 *   (p(y), x === y, p(x)) ⊢ p(x)
 * with the extra p(x). Subsequent Restate steps then fail.
 *
 * Run with: sbt "lisa-sets/runMain lisa.maths.SetTheory.CongruenceTests"
 */
object CongruenceTests extends lisa.Main {

  // ── Uninterpreted symbols ─────────────────────────────────────
  private val x, y, z, a, b, c: Variable[Ind] = variable[Ind]
  private val f: Variable[Ind >>: Ind] = variable[Ind >>: Ind]
  private val p: Variable[Ind >>: Prop] = variable[Ind >>: Prop]
  private val q: Variable[Ind >>: Prop] = variable[Ind >>: Prop]
  private val r: Variable[Ind >>: Prop] = variable[Ind >>: Prop]
/*
  // ═══════════════════════════════════════════════════════════════
  //  Baseline: standalone Congruence (no premises) — should work
  // ═══════════════════════════════════════════════════════════════

  // Test 0: Sanity check — standalone Congruence, no premise
  val test0 = Theorem((p(y), x === y) |- p(x)) {
    have((p(y), x === y) |- p(x)) by Congruence
  }

  // ═══════════════════════════════════════════════════════════════
  //  Single premise — one LHS formula to derive by congruence
  // ═══════════════════════════════════════════════════════════════

  // Test 1: Replace p(x) by p(y) + equality
  //   premise: p(x) ⊢ p(x)
  //   goal:    (p(y), x === y) ⊢ p(x)
  val test1 = Theorem((p(y), x === y) |- p(x)) {
    have(p(x) |- p(x)) by Restate
    thenHave((p(y), x === y) |- p(x)) by Congruence
  }

  // Test 2: Congruence under unary function
  //   premise: p(f(x)) ⊢ p(f(x))
  //   goal:    (p(f(y)), x === y) ⊢ p(f(x))
  val test2 = Theorem((p(f(y)), x === y) |- p(f(x))) {
    have(p(f(x)) |- p(f(x))) by Restate
    thenHave((p(f(y)), x === y) |- p(f(x))) by Congruence
  }

  // Test 3: Equality between function result and variable (like dom(R) === d)
  //   premise: p(f(x)) ⊢ p(f(x))
  //   goal:    (p(y), f(x) === y) ⊢ p(f(x))
  val test3 = Theorem((p(y), f(x) === y) |- p(f(x))) {
    have(p(f(x)) |- p(f(x))) by Restate
    thenHave((p(y), f(x) === y) |- p(f(x))) by Congruence
  }

  // Test 4: Deep nesting f(f(x))
  //   premise: p(f(f(x))) ⊢ p(f(f(x)))
  //   goal:    (p(f(f(y))), x === y) ⊢ p(f(f(x)))
  val test4 = Theorem((p(f(f(y))), x === y) |- p(f(f(x)))) {
    have(p(f(f(x))) |- p(f(f(x)))) by Restate
    thenHave((p(f(f(y))), x === y) |- p(f(f(x)))) by Congruence
  }

  // ═══════════════════════════════════════════════════════════════
  //  Single premise — multiple LHS formulas to derive
  // ═══════════════════════════════════════════════════════════════

  // Test 5: Two LHS formulas, same equality
  //   premise: (p(x), q(x)) ⊢ r(x)    [sorry]
  //   goal:    (p(y), q(y), x === y) ⊢ r(x)
  val test5 = Theorem((p(y), q(y), x === y) |- r(x)) {
    have((p(x), q(x)) |- r(x)) subproof { sorry }
    thenHave((p(y), q(y), x === y) |- r(x)) by Congruence
  }

  // Test 6: Two LHS formulas, independent equalities
  //   premise: (p(x), q(y)) ⊢ r(x)    [sorry]
  //   goal:    (p(a), q(b), x === a, y === b) ⊢ r(x)
  val test6 = Theorem((p(a), q(b), x === a, y === b) |- r(x)) {
    have((p(x), q(y)) |- r(x)) subproof { sorry }
    thenHave((p(a), q(b), x === a, y === b) |- r(x)) by Congruence
  }

  // Test 7: Mixed — one formula already present, one needs congruence
  //   premise: (p(x), q(y)) ⊢ r(x)    [sorry]
  //   goal:    (p(x), q(b), y === b) ⊢ r(x)
  val test7 = Theorem((p(x), q(b), y === b) |- r(x)) {
    have((p(x), q(y)) |- r(x)) subproof { sorry }
    thenHave((p(x), q(b), y === b) |- r(x)) by Congruence
  }

  // ═══════════════════════════════════════════════════════════════
  //  Congruence + Restate (the real failure pattern)
  // ═══════════════════════════════════════════════════════════════

  // Test 8: Congruence then Restate to merge into conjunction
  //   If Congruence leaks p(x), the Restate fails because it sees
  //   extra formulas that don't match the conjunction target.
  val test8 = Theorem((p(y) /\ (x === y)) |- p(x)) {
    have(p(x) |- p(x)) by Restate
    thenHave((p(y), x === y) |- p(x)) by Congruence
    thenHave((p(y) /\ (x === y)) |- p(x)) by Restate
  }*/

  // ═══════════════════════════════════════════════════════════════
  //  Two explicit premises (Congruence.from)
  // ═══════════════════════════════════════════════════════════════

  // Test 9: Two premises, each with one LHS formula that leaks
  //   fact1: p(x) ⊢ r(x)   [sorry]
  //   fact2: q(y) ⊢ r(x)   [sorry]
  //   goal:  (p(a), q(b), x === a, y === b) ⊢ r(x)
  //
  //   Bug: leaks both p(x) and q(y) into result
  val test9 = Theorem((p(a), q(b), x === a, y === b) |- r(x)) {
    val fact1 = have(p(x) |- r(x)) subproof { sorry }
    val fact2 = have(q(y) |- r(x)) subproof { sorry }
    have((p(a), q(b), x === a, y === b) |- r(x)) by Congruence.from(fact1, fact2)
  }

  val test10 = Theorem((p(a), x === a) |- q(a)) {
    val fact1 = have(p(x) |- x === y) subproof { sorry }
    val fact2 = have(p(y) |- q(y)) subproof { sorry }
    have((p(a), x === a) |- q(a)) by Congruence.from(fact1, fact2)
  }

  
}
