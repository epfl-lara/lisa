package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntArrayList

import Core.*
import lisa.automation.superposition.ordering.*

/** Every generating inference the loop performs on a given clause: ordinary resolution and superposition against
  * the active set, and factoring, equality resolution and equality factoring on the clause itself. [[generate]]
  * is the only entry point, and runs them in that order.
  *
  * The counterpart of [[Simplifier]], which owns the deleting and shrinking half.
  *
  * Partners come from the [[ActiveSet]]'s indices. The class handles eligibility, not the rules' themselves: it
  * passes only the literal positions the selection admits, and [[Inference]] and [[Superposition]] check only the
  * term-orientation conditions. */
final class Generator(bank: TermBank, trail: Trail, active: ActiveSet, opts: SearchOptions)(emit: Clause => Boolean):
  import opts.*

  // Ordering used only for the (optional) post-unification σ-maximality check on factors.
  private val kbo: KBO = bank.order.kbo

  /** Every inference between `gc` (already in the active set, so the self-pairs fire) and the active clauses,
    * plus every inference of `gc` with itself. `gSel` is `gc`'s literal selection, computed by the caller since
    * the indices key on it. `true` as soon as some conclusion is the empty clause. */
  def generate(gc: Clause, gSel: Array[Int]): Boolean =
    if resolveGiven(gc, gSel) then return true
    if superpositionOn && superposeGiven(gc, gSel, gc.rewriteSources(bank)) then return true
    if factorGiven(gc, gSel) then return true
    if equality && equalityInferences(gc, gSel) then return true
    false

  // --- ordinary resolution --------------------------------------------------------------------------------

  /** Resolution of `gc` against the active set: for each of its selected non-equality literals, query the
    * *opposite*-polarity literal index with the atom, so every candidate is already complementary, and confirm
    * each with [[Inference.resolve]], which re-checks complementarity and does the real unification. */
  private def resolveGiven(gc: Clause, gSel: Array[Int]): Boolean =
    var stop = false // set inside the retrieval callback, where `return` is not available
    var gi = 0
    while gi < gSel.length && !stop do
      val iLit: Int = gSel(gi)
      val lit: Literal = gc.literals(iLit)
      if !bank.isEquality(lit) then // equalities go to superposition and equality resolution, not here
        active.resolutionPartners(bank.isPositive(lit), bank.atomOf(lit)) { e =>
          if !stop then
            Inference.resolve(bank, trail, gc, iLit, e.clause, e.litIndex) match
              case Some(r) => stop = emit(r)
              case None => ()
        }
      gi += 1
    stop

  // --- superposition --------------------------------------------------------------------------------------

  /** Superposition of `gc` against the active set, in both directions, with partners from the fingerprint
   *  indices. `gc` is already in both, so Pass 1 (gc's equations rewriting into active subterms) also covers the
   *  `gc`-into-`gc` self-pair; Pass 2 (active equations rewriting into gc's subterms) therefore *skips*
   *  candidates from `gc` itself. `gcSources` is `gc.rewriteSources`, passed in because the caller has it. */
  private def superposeGiven(gc: Clause, gSel: Array[Int], gcSources: Array[RewriteSource]): Boolean =
    var stop = false // set inside the retrieval callbacks, where `return` is not available
    // Pass 1: gc supplies the equation; query the into-index with each rewrite it offers.
    var s = 0
    while s < gcSources.length && !stop do
      val src: RewriteSource = gcSources(s)
      active.intoCandidates(src.lhs) { e =>
        if !stop then stop = superposeVerified(gc, src.lit, src.side, e.clause, e.litIndex, IntArrayList.wrap(e.pos))
      }
      s += 1
    // Pass 2: active clauses supply the equation; query the from-index with each of gc's non-variable subterms.
    var gi = 0
    while gi < gSel.length && !stop do
      val iInto: Int = gSel(gi)
      Superposition.foreachSubterm(bank, bank.atomOf(gc.literals(iInto))) { (u, path) =>
        active.fromCandidates(u) { e =>
          if !stop && e.clause.id != gc.id then // gc-into-gc already done in Pass 1
            stop = superposeVerified(e.clause, e.litIndex, e.side, gc, iInto, path) // live stack: `superpose` snapshots it
        }
        stop // stop the subterm walk on refutation
      }
      gi += 1
    stop

  /** Verify + build one located superposition: unify `fromC`'s side `fromSide` with `intoC`'s subterm at `pos`,
   *  then the build-only [[Superposition.superpose]] and `emit`. Restores the trail. `true` on refutation.
   *
   *  `pos` may be a caller's live subterm-walk stack, so nothing here retains it: [[Superposition.superpose]]
   *  snapshots it, and only for the inferences that fire. */
  private def superposeVerified(fromC: Clause, iFrom: Int, fromSide: Int, intoC: Clause, iInto: Int, pos: IntArrayList): Boolean =
    val l: Term = bank.arg(bank.atomOf(fromC.literals(iFrom)), fromSide)
    val u: Term = Superposition.subtermAt(bank, bank.atomOf(intoC.literals(iInto)), pos)
    val saved: Int = trail.save()
    var stop = false
    if trail.unify(l, 0, u, 1) then
      Superposition.superpose(bank, trail, fromC, iFrom, fromSide, intoC, iInto, pos) match
        case Some(rr) => stop = emit(rr)
        case None => ()
    trail.restore(saved)
    stop

  // --- factoring and the unary equality rules -------------------------------------------------------------

  /** Positive factoring on `gc`: each unordered pair of distinct selected, positive, non-equality literals,
    * once. Equality literals are factored by [[Superposition.equalityFactoring]] instead.
    *
    * Pairing within the selected set loses nothing: a literal that unifies with a selected (maximal) one is
    * itself maximal, hence also selected. When [[SearchOptions.factorAfterCheck]] is on, a factor whose kept
    * literal is no longer maximal under the unifier is dropped. */
  private def factorGiven(gc: Clause, gSel: Array[Int]): Boolean =
    var a = 0
    while a < gSel.length do
      val i: Int = gSel(a)
      if bank.isPositive(gc.literals(i)) && !bank.isEquality(gc.literals(i)) then
        var b = a + 1
        while b < gSel.length do
          val j: Int = gSel(b)
          if !bank.isEquality(gc.literals(j)) then
            Inference.factor(bank, trail, gc, i, j) match
              case Some(f) =>
                // `factor` drops `j`, so the kept literal `i` keeps its index -- but only because `i < j`, which
                // holds since `gSel` is ascending (every selector returns a singleton or the maximal literals in
                // clause order). Asserted, since a selector ordering its indices otherwise would break it silently.
                assert(i < j, s"literal selection must be ascending: got i=$i, j=$j")
                if (!factorAfterCheck || keptMaximal(f, i)) && emit(f) then return true
              case None => ()
          b += 1
      a += 1
    false

  /** Equality resolution and equality factoring on `gc`, both unary: each enumerates every applicable literal
   *  over the eligible set. `exists` emits the conclusions in list order and stops at the first `□`. */
  private def equalityInferences(gc: Clause, gSel: Array[Int]): Boolean =
    Superposition.equalityResolution(bank, trail, gc, gSel).exists(emit) ||
      Superposition.equalityFactoring(bank, trail, gc, gSel).exists(emit)

  /** σ-maximality after-check: in the (already σ-applied) factor `f`, the kept literal must be maximal --
   *  no other literal's atom is strictly KBO-greater than it. (Maximal, not strictly: the merged literal
   *  may have an equal twin.) */
  private def keptMaximal(f: Clause, keptIdx: Int): Boolean =
    val keptAtom: Term = bank.atomOf(f.literals(keptIdx))
    var k = 0
    while k < f.literals.length do
      if k != keptIdx && kbo.compare(bank.atomOf(f.literals(k)), keptAtom) == Cmp.Gt then return false
      k += 1
    true
