package lisa.automation.superposition

import Core.*

/**
 * Generating inference rules for the DISCOUNT loop: binary resolution and factoring, both with
 * unification. Each rule reuses the Phase-0 [[Trail]] (two scopes for resolution, one for factoring)
 * and a fresh [[Trail.Applier]] to instantiate and densely renumber the conclusion's variables, and
 * records a [[Justification]] on the resulting clause for later proof reconstruction.
 *
 * The functions take explicit literal indices (the loop picks them from each clause's stored
 * `selected` set, computed by its [[LiteralSelector]]); each unifies, builds the conclusion, then
 * restores the trail to its incoming state, so the caller's trail is left untouched whether or not
 * the inference fires.
 */
object Inference:

  /**
   * Binary resolution: resolve `c1`'s literal `i1` against `c2`'s literal `i2`, which must be
   * complementary (opposite polarity). On success returns the resolvent
   * `(c1 \ {i1} ∪ c2 \ {i2})σ`, with `σ` the mgu of the two atoms; `None` if they aren't
   * complementary or don't unify. The two parents' variables are kept apart by scope (0 vs 1), so
   * shared variable numbers don't clash. Duplicate literals are *not* removed here (left to
   * canonicalisation), matching the reference provers.
   */
  def resolve(bank: TermBank, trail: Trail, c1: Clause, i1: Int, c2: Clause, i2: Int): Option[Clause] =
    val l1: Literal = c1.literals(i1)
    val l2: Literal = c2.literals(i2)
    if bank.isPositive(l1) == bank.isPositive(l2) then None // not complementary
    else
      val saved: Int = trail.save()
      val result: Option[Clause] =
        if !trail.unify(bank.atomOf(l1), 0, bank.atomOf(l2), 1) then None
        else
          val applier = trail.applier()
          val out: Array[Literal] = new Array[Literal](c1.literals.length - 1 + c2.literals.length - 1)
          var n = 0
          var i = 0
          while i < c1.literals.length do
            if i != i1 then
              out(n) = applier.applyLit(c1.literals(i), 0)
              n += 1
            i += 1
          i = 0
          while i < c2.literals.length do
            if i != i2 then
              out(n) = applier.applyLit(c2.literals(i), 1)
              n += 1
            i += 1
          Some(bank.mkClause(out, Justification.Resolution(c1, i1, c2, i2)))
      trail.restore(saved)
      result

  /**
   * Canonicalise a clause for insertion into the passive set: sort its literals into
   * [[Core.compareLiterals]] order, drop duplicate literals, and detect tautologies (complementary
   * literals `L`/`¬L`). Returns `None` if the clause is a tautology (discard it), the **same** clause
   * if it is already canonical, or a new clause carrying a [[Justification.Canonicalization]] step
   * whose parent is `c`. That parent is retained only for reconstruction and is **not** itself
   * inserted into the clause sets.
   *
   * Equality trivials (`s = s`, `s ≠ s`) and variable normalisation are intentionally not handled
   * yet (Phase 3 and Phase 2 respectively).
   */
  def canonicalize(bank: TermBank, c: Clause): Option[Clause] =
    // Discard a clause containing a positive trivial equality `s = s` (a tautology). A negative `s ≠ s` is
    // left for equality resolution to close (it carries a proper Justification). Scanned before the `n <= 1`
    // early return so unit `{s = s}` clauses are caught too.
    var t = 0
    while t < c.literals.length do
      val l: Literal = c.literals(t)
      if bank.isPositive(l) then
        val a: Term = bank.atomOf(l)
        if bank.headSymbol(a) == EqualitySymbol && bank.arg(a, 0) == bank.arg(a, 1) then return None
      t += 1
    val n: Int = c.literals.length
    if n <= 1 then Some(c) // nothing to sort, dedup, or make complementary
    else
      val lits: Array[Literal] = c.literals.clone()
      bank.sortLiterals(lits) // canonical literal order, in place (fastutil primitive quicksort)
      // lits(0) is always kept; `count` tracks the index of the last kept literal. Compact the rest
      // in place, comparing each literal to the last kept one (sorting keeps duplicates and
      // complementary pairs adjacent, so this one pass suffices).
      var count = 0
      var i = 1
      while i < n do
        val l: Literal = lits(i)
        if bank.atomOf(l) == bank.atomOf(lits(count)) then
          if l != lits(count) then return None // same atom, opposite polarity: tautology
          // else duplicate literal: drop it
        else
          count += 1
          lits(count) = l
        i += 1
      val kept = count + 1 // number of literals retained
      // did canonicalisation change anything? a dropped duplicate, or a reorder by the sort
      var changed = kept < n
      if !changed then
        var k = 0
        while k < n && !changed do
          if lits(k) != c.literals(k) then changed = true
          k += 1
      if !changed then Some(c)
      else
        // reuse the (already canonical) clone when nothing was dropped; truncate only on dedup
        val canonical: Array[Literal] = if kept == n then lits else lits.take(kept)
        Some(bank.mkClause(canonical, Justification.Canonicalization(c)))

  /**
   * Factoring: merge `c`'s literals `i` and `j` (distinct, same polarity) by unifying their atoms.
   * On success returns `(c \ {j})σ` -- literal `j` is dropped, having become identical to `i` under
   * `σ`. `None` if they differ in polarity or don't unify.
   */
  def factor(bank: TermBank, trail: Trail, c: Clause, i: Int, j: Int): Option[Clause] =
    require(i != j, "factoring needs two distinct literals")
    val li: Literal = c.literals(i)
    val lj: Literal = c.literals(j)
    if bank.isPositive(li) != bank.isPositive(lj) then None // different polarity
    else
      val saved: Int = trail.save()
      val result: Option[Clause] =
        if !trail.unify(bank.atomOf(li), 0, bank.atomOf(lj), 0) then None
        else
          val applier = trail.applier()
          val out: Array[Literal] = new Array[Literal](c.literals.length - 1)
          var n = 0
          var k = 0
          while k < c.literals.length do
            if k != j then
              out(n) = applier.applyLit(c.literals(k), 0)
              n += 1
            k += 1
          Some(bank.mkClause(out, Justification.Factoring(c, i, j)))
      trail.restore(saved)
      result
