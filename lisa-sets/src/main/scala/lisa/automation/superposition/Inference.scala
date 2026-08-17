package lisa.automation.superposition

import Core.*

/** Binary resolution and factoring, plus the canonicalisation of new clauses. Each rule takes
  * explicit literal indices, which the loop draws from the clause's selection, unifies, builds the conclusion
  * through an [[Trail.Applier]] that renumbers its variables, records a [[Justification]], and restores the trail. */
object Inference:

  /** Binary resolution: resolve `c1`'s literal `i1` against `c2`'s literal `i2`, which must be
    * complementary (opposite polarity). On success returns the resolvent
    * `(c1 \ {i1} ∪ c2 \ {i2})σ`, with `σ` the mgu of the two atoms; `None` if they aren't
    * complementary or don't unify. The two parents' variables are kept apart by scope (0 vs 1), so
    * shared variable numbers don't clash. Duplicate literals are *not* removed here (left to
    * canonicalisation), matching the reference provers. */
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
          val n1 = applier.copyLitsExcept(c1.literals, i1, 0, out, 0)
          applier.copyLitsExcept(c2.literals, i2, 1, out, n1)
          Some(bank.mkClause(out, Justification.Resolution(c1, i1, c2, i2)))
      trail.restore(saved)
      result

  /** Sort a clause's literals, drop duplicates and detect tautologies. Returns `None` for a tautology, the
    * same clause if it was already canonical, or a new one recording a [[Justification.Canonicalization]].
    *
    * A positive `s = s` makes the clause a tautology, but a negative `s ≠ s` is left in place for equality
    * resolution to close with a proper justification. Clauses are not normalised up to variable renaming, so
    * two variants of one clause remain distinct. */
  def canonicalize(bank: TermBank, c: Clause): Option[Clause] =
    var t = 0
    while t < c.literals.length do
      val l: Literal = c.literals(t)
      if bank.isPositive(l) then
        val a: Term = bank.atomOf(l)
        if bank.isEqualityAtom(a) && bank.arg(a, 0) == bank.arg(a, 1) then return None
      t += 1
    val n: Int = c.literals.length
    if n <= 1 then Some(c) // nothing to sort, dedup, or make complementary
    else
      val lits: Array[Literal] = c.literals.clone()
      bank.sortLiterals(lits) // canonical literal order, in place (fastutil primitive quicksort)
      // lits(0) is always kept; `count` tracks the index of the last kept literal. Compact the rest
      // in place, comparing each literal to the last kept one.
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

  /** Factoring: merge `c`'s literals `i` and `j` (distinct, same polarity) by unifying their atoms.
    * On success returns `(c \ {j})σ` -- literal `j` is dropped, having become identical to `i` under
    * `σ`. `None` if they differ in polarity or don't unify. */
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
          applier.copyLitsExcept(c.literals, j, 0, out, 0)
          Some(bank.mkClause(out, Justification.Factoring(c, i, j)))
      trail.restore(saved)
      result
