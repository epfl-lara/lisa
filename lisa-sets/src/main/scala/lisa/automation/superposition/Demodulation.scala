package lisa.automation.superposition

import scala.collection.mutable
import it.unimi.dsi.fastutil.ints.IntArrayList

import Core.*

/**
 * Demodulation (Phase 4 Step 3): simplification by rewriting with **positive unit equalities**. Forward
 * demodulation normal-forms a clause against the active unit equations; backward demodulation rewrites
 * active clauses with a newly arrived unit equality. Each rewrite step replaces a subterm by a strictly
 * smaller instance (the reduction ordering guarantees termination), so a clause is normalised by repeated
 * single steps; each step records a [[Justification.Demodulation]] chained to the previous clause.
 *
 * Matching (not unification) drives it: the rule's LHS is a generalisation of the rewritten subterm, so
 * only the rule's variables bind (via [[Trail.matchTerm]]). The result is built through a [[Trail.Applier]]
 * exactly as the generating inferences do, so the target clause's variables are consistently renumbered.
 *
 * **Redundancy gate** ([[isPremiseRedundant]], encompassment demodulation à la Vampire / E's restricted
 * rewriting): a rewrite may *delete/replace* its premise (simplify) except when it rewrites a whole side of
 * a maximal positive **unit** equality with a renaming (variant) matcher; there the premise is not
 * redundant and the rewrite is **skipped** (superposition covers that inference). Everywhere else — inside
 * a subterm, a non-equality/negative literal, a multi-literal clause, a proper (non-renaming) instance, or
 * rewriting the larger side downward — the premise is always redundant, so demodulation simplifies freely.
 */
object Demodulation:

  /** A usable rewrite direction extracted from a positive unit equality clause: `lhs → rhs`. `lhsVars` are
   *  the distinct variables of `lhs`, precomputed once (they're invariant) for the renaming redundancy check. */
  final case class Rule(source: Clause, side: Int, lhs: Term, rhs: Term, oriented: Boolean, lhsVars: Array[Term])

  /** Distinct variable terms occurring in `t`, in first-occurrence order. */
  private def varsOf(bank: TermBank, t: Term): List[Term] =
    val acc = mutable.LinkedHashSet.empty[Term]
    def go(x: Term): Unit =
      if bank.isVar(x) then acc += x
      else
        var i = 0; val n = bank.arity(x)
        while i < n do { go(bank.arg(x, i)); i += 1 }
    go(t); acc.toList

  /**
   * The usable rewrite directions of `eq` as a demodulator: `Nil` unless `eq` is a positive unit equality.
   * Oriented equations rewrite from the `Gt` side; unoriented ones rewrite from a side only if that side's
   * variables cover the other's (so no fresh variable is introduced) and it is not itself a variable.
   */
  def rules(bank: TermBank, order: Order, eq: Clause): List[Rule] =
    if eq.literals.length != 1 then Nil
    else
      val lit = eq.literals(0)
      val atom = bank.atomOf(lit)
      if !bank.isPositive(lit) || !order.isEqualityAtom(atom) then Nil
      else
        val s0 = bank.arg(atom, 0); val s1 = bank.arg(atom, 1)
        def mk(side: Int, lhs: Term, rhs: Term, oriented: Boolean): Rule =
          Rule(eq, side, lhs, rhs, oriented, varsOf(bank, lhs).toArray)
        order.orient(atom) match
          case Cmp.Gt => if bank.isVar(s0) then Nil else List(mk(0, s0, s1, true))
          case Cmp.Lt => if bank.isVar(s1) then Nil else List(mk(1, s1, s0, true))
          case Cmp.Eq => Nil
          case Cmp.Inc =>
            val v0 = varsOf(bank, s0).toSet; val v1 = varsOf(bank, s1).toSet
            var rs: List[Rule] = Nil
            // side 0 as LHS needs vars(s1) ⊆ vars(s0); side 1 as LHS needs vars(s0) ⊆ vars(s1)
            if !bank.isVar(s1) && v0.subsetOf(v1) then rs = mk(1, s1, s0, false) :: rs
            if !bank.isVar(s0) && v1.subsetOf(v0) then rs = mk(0, s0, s1, false) :: rs
            rs

  /** All usable demodulator directions of a set of (candidate) unit equations, as a re-iterable array
   *  (the rule set is scanned once per subterm per rewrite step, so it must be replayable — an array is
   *  iterated by index in `rewriteOnce`, allocating no iterator). */
  def rulesOf(bank: TermBank, order: Order, eqs: Iterable[Clause]): Array[Rule] =
    eqs.iterator.flatMap(rules(bank, order, _)).toArray

  /**
   * Forward demodulation: rewrite `clause` to a normal form w.r.t. `activeUnitEqs`. Returns the same clause
   * (by identity) if nothing applies, else the normalised clause whose justification chains the steps.
   */
  def forwardDemodulate(bank: TermBank, trail: Trail, order: Order, clause: Clause, activeUnitEqs: Iterable[Clause]): Clause =
    normalForm(bank, trail, order, clause, rulesOf(bank, order, activeUnitEqs))

  /** Forward demodulation against a pre-extracted rule set (the loop caches these). */
  def normalForm(bank: TermBank, trail: Trail, order: Order, clause: Clause, rules: Array[Rule]): Clause =
    if rules.isEmpty then clause
    else
      var cur = clause
      var step = rewriteOnce(bank, trail, order, cur, rules)
      while step.isDefined do
        cur = step.get
        step = rewriteOnce(bank, trail, order, cur, rules)
      cur

  /**
   * Backward demodulation: a new positive unit equality `newEq` arrives; rewrite each clause in `active`
   * whose subterms it can reduce. Returns the `(removed, replacement)` pairs (the loop removes the original
   * and re-inserts the replacement).
   */
  def backwardDemodulate(bank: TermBank, trail: Trail, order: Order, newEq: Clause, active: Iterable[Clause]): List[(Clause, Clause)] =
    val rs = rules(bank, order, newEq).toArray
    if rs.isEmpty then Nil
    else
      val out = mutable.ListBuffer.empty[(Clause, Clause)]
      for c <- active do
        val r = normalForm(bank, trail, order, c, rs)
        if r.id != c.id then out += ((c, r))
      out.toList

  // --- one rewrite step --------------------------------------------------------------------------

  /** The first applicable single rewrite of `c` by any rule, leftmost-outermost over subterm positions.
   *  Enumerates positions with a reused stack ([[Superposition.foreachSubterm]]); a position is only
   *  materialised (in `tryRewrite`) when a rewrite fires. */
  private def rewriteOnce(bank: TermBank, trail: Trail, order: Order, c: Clause, rules: Array[Rule]): Option[Clause] =
    var result: Option[Clause] = None
    var iLit = 0
    while iLit < c.literals.length && result.isEmpty do
      val li: Int = iLit
      val atom: Term = bank.atomOf(c.literals(li))
      Superposition.foreachSubterm(bank, atom) { (u, path) =>
        var ri = 0
        while ri < rules.length && result.isEmpty do
          result = tryRewrite(bank, trail, order, c, li, path, u, rules(ri))
          ri += 1
        result.isDefined // stop the traversal once a rewrite is found
      }
      iLit += 1
    result

  private def tryRewrite(bank: TermBank, trail: Trail, order: Order,
                         c: Clause, iLit: Int, path: IntArrayList, u: Term, rule: Rule): Option[Clause] =
    val saved = trail.save()
    val result: Option[Clause] =
      if !trail.matchTerm(rule.lhs, 0, u, 1) then None // match rule LHS (scope 0) onto the subterm (scope 1)
      else
        val ap: trail.Applier = trail.applier()
        val lS: Term = ap.apply(rule.lhs, 0)
        val rS: Term = ap.apply(rule.rhs, 0)
        // orientation re-check on the instance (skip for an already-oriented rule)
        if !rule.oriented && order.kbo.compare(lS, rS) != Cmp.Gt then None
        else
          val iLitLit: Literal = c.literals(iLit) // the rewritten literal + its atom, read once for the gate and the build
          val iLitAtom: Term = bank.atomOf(iLitLit)
          if !isPremiseRedundant(bank, order, ap, c, iLitLit, iLitAtom, path, rS, rule) then None
          else
            val pos: Array[Int] = path.toIntArray // materialise the position only now that the rewrite fires
            val newLits = new Array[Literal](c.literals.length)
            var k = 0
            while k < c.literals.length do
              newLits(k) =
                if k == iLit then // the rewritten literal: instantiate its atom, then replace u by r at `pos`
                  bank.mkLiteral(Superposition.replaceAt(bank, ap.apply(iLitAtom, 1), pos, rS), bank.isPositive(iLitLit))
                else ap.applyLit(c.literals(k), 1)
              k += 1
            Some(bank.mkClause(newLits, Justification.Demodulation(c, iLit, pos, rule.source, rule.side)))
    trail.restore(saved)
    result

  /**
   * Whether rewriting `c`'s literal `iLit` at position `path` (yielding instance `rS` on that side) keeps
   * the premise redundant — i.e. the rewrite may simplify (delete/replace) `c`. Encompassment mode. Reads
   * the live position stack (no snapshot): only its depth and first index matter.
   */
  private def isPremiseRedundant(bank: TermBank, order: Order, ap: Trail#Applier,
                                 c: Clause, lit: Literal, atom: Term, path: IntArrayList, rS: Term, rule: Rule): Boolean =
    val wholeSide = order.isEqualityAtom(atom) && path.size() == 1
    if !wholeSide then true // rewriting inside a subterm / a non-equality literal: always redundant
    else if !bank.isPositive(lit) || c.literals.length != 1 then true // check only bites on positive unit equalities
    else
      val side: Int = path.getInt(0)
      val otherS = ap.apply(bank.arg(atom, 1 - side), 1) // the untouched side, instantiated
      // rewrote the larger side downward ⇒ redundant; else redundant iff the matcher is a proper instance
      order.kbo.compare(rS, otherS) == Cmp.Lt || !matcherIsRenaming(bank, ap, rule.lhsVars)

  /** Whether the matcher σ, restricted to the rule's LHS variables (precomputed on the [[Rule]]), is a
   *  variable renaming (injective onto variables). */
  private def matcherIsRenaming(bank: TermBank, ap: Trail#Applier, lhsVars: Array[Term]): Boolean =
    val images = lhsVars.map(v => ap.apply(v, 0))
    images.forall(bank.isVar) && images.distinct.length == images.length
