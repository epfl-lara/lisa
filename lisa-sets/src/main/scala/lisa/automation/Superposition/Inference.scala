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
          def inst(lit: Literal, scope: Scope): Literal =
            bank.mkLiteral(applier.apply(bank.atomOf(lit), scope), bank.isPositive(lit))
          val out: Array[Literal] = new Array[Literal](c1.literals.length - 1 + c2.literals.length - 1)
          var n = 0
          var i = 0
          while i < c1.literals.length do
            if i != i1 then
              out(n) = inst(c1.literals(i), 0)
              n += 1
            i += 1
          i = 0
          while i < c2.literals.length do
            if i != i2 then
              out(n) = inst(c2.literals(i), 1)
              n += 1
            i += 1
          Some(bank.mkClause(out, Justification.Resolution(c1, i1, c2, i2)))
      trail.restore(saved)
      result

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
          def inst(lit: Literal): Literal =
            bank.mkLiteral(applier.apply(bank.atomOf(lit), 0), bank.isPositive(lit))
          val out: Array[Literal] = new Array[Literal](c.literals.length - 1)
          var n = 0
          var k = 0
          while k < c.literals.length do
            if k != j then
              out(n) = inst(c.literals(k))
              n += 1
            k += 1
          Some(bank.mkClause(out, Justification.Factoring(c, i, j)))
      trail.restore(saved)
      result
