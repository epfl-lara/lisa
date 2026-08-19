package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import scala.collection.mutable

import Core.*
import lisa.automation.superposition.index.*

/** How much each simplification fired during a saturation: observability, and what the ablations read. */
final class SimplificationStats:
  var forwardSubsumed: Int = 0
  var backwardSubsumed: Int = 0
  var forwardUnitDeleted: Int = 0
  var backwardUnitDeleted: Int = 0
  var forwardSubsumptionResolved: Int = 0 // multi-literal-side forward SR
  var backwardSubsumptionResolved: Int = 0
  var condensed: Int = 0

/** Every simplification step of the loop, in both directions. [[forward]] discards or shrinks the clause being
  * selected; [[backwardSubsume]] and [[backwardDemodulate]] delete or shrink active clauses using the given,
  * before it joins them so that it never simplifies itself; [[condense]] replaces a clause by a shorter factor
  * of itself. */
final class Simplifier(bank: TermBank, trail: Trail, active: ActiveSet, opts: SearchOptions):
  import opts.*

  /** How much each simplification fired. One `Simplifier` serves one saturation, so these are never reset. */
  val stats: SimplificationStats = new SimplificationStats

  // --- reusable candidate buffers -------------------------------------------------------------------------
  //
  // One buffer per retrieval phase (named in the trailing comments), holding that phase's candidates, plus
  // `seenIds` to deduplicate within one phase. A phase clears its own buffer, fills it during the index
  // descent, and acts only once the descent has returned, which is what [[FeatureVectorIndex]] requires of a
  // retrieval callback.

  private val unitCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty // forward unit deletion
  private val srCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty //   forward SR
  private val bwVictims: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty // backward subsumption
  private val bwCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty //   backward SR
  private val shrunk: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty //    backward replacements, emitted
  private val demodCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty // backward demodulation targets
  private val seenIds: IntOpenHashSet = new IntOpenHashSet() // dedup within one collection phase only

  /** Visit `use(query, i)` for each literal `i` of `c`, where `query` is a throwaway clause carrying `c` with
    * literal `i`'s polarity flipped.
    *
    * This is the "char-2" characterisation: a stored clause subsumption-resolves `c` on `Lᵢ`
    * exactly when it subsumes `c` with `Lᵢ` flipped, and a unit deletes `Lᵢ` exactly when it subsumes `{¬Lᵢ}`. */
  private def foreachFlipped(c: Clause, singleton: Boolean)(use: (QueryClause, Int) => Unit): Unit =
    var i = 0
    while i < c.literals.length do
      val lits: Array[Literal] =
        if singleton then Array(bank.negate(c.literals(i)))
        else
          val ls: Array[Literal] = c.literals.clone()
          ls(i) = bank.negate(ls(i))
          ls
      use(bank.mkQueryClause(lits), i)
      i += 1

  // --- clause-local ---------------------------------------------------------------------------------------

  /** Replace `c` by an equivalent shorter factor of itself, if one exists and [[SearchOptions.condensation]]
    * is on. Clause-local: no active-set scan, applied once at creation. Cannot produce `□` or a tautology. */
  def condense(c: Clause): Clause =
    if !condensation then c
    else
      val cd: Clause = Subsumption.condense(bank, trail, c)
      if cd ne c then stats.condensed += 1
      cd

  // --- forward --------------------------------------------------------------------------------------------

  /** Forward simplify `m` against the active set. If
    * some active clause subsumes `m`, return `None`; otherwise apply subsumption resolution, returning the
    * possibly-shrunk clause or `Some(□)` if a resolution closed it. Forward subsumption asks the index an
    * *existence* question, so its `≤`-cone descent stops at the first verified subsumer; unit deletion
    * dispatches on the unit count ([[SearchOptions.forwardUnitDeletionIndexThreshold]]). */
  def forward(m0: Clause): Option[Clause] =
    var m: Clause = m0
    if forwardSubsumption then
      if active.existsSubsumer(m)(c => Subsumption.subsumes(bank, trail, c, m)) then
        stats.forwardSubsumed += 1
        return None
    if forwardUnitDeletion then
      if active.unitClauses.length <= forwardUnitDeletionIndexThreshold then
        // Few units: scan the active-unit sublist directly (near-zero fixed overhead).
        m = applyUnitDeletions(active.unitClauses, m)
        if m.isEmpty then return Some(m)
      else
        // Many units: gather the candidate units via the index. A unit deletes a literal `K` of `m` iff it
        // subsumes the singleton `{¬K}`, so query the ≤-cone of each `{¬K}`, then verify with `subsumes`.
        collectSubsumersOfFlipped(m, singleton = true, units = true, unitCands)
        if unitCands.nonEmpty then
          m = applyUnitDeletions(unitCands, m)
          if m.isEmpty then return Some(m)
    if forwardSubsumptionResolution then
      m = forwardSubsumptionResolveChar2(m)
      if m.isEmpty then return Some(m)
    Some(m)

  /** Collect into `out` the active clauses that subsume some one-literal-flipped form of `m`, deduped by id:
    * the simplifiers of `m`, by the char-2 characterisation ([[foreachFlipped]]). `units` picks which size of
    * simplifier is wanted -- units delete a literal outright, longer clauses resolve one away -- and
    * `singleton` picks the query shape that suits it. Collects only: the callers act after the descent. */
  private def collectSubsumersOfFlipped(m: Clause, singleton: Boolean, units: Boolean,
                                        out: mutable.ArrayBuffer[Clause]): Unit =
    seenIds.clear(); out.clear()
    foreachFlipped(m, singleton) { (query, _) =>
      active.subsumerCandidates(query) { c =>
        val sized: Boolean = if units then c.size == 1 else c.size > 1
        if sized && Subsumption.subsumes(bank, trail, c, query) && seenIds.add(c.id) then out += c
      }
    }

  /** Apply unit deletion to `m` by each candidate unit in `cands`, in order: each `subsumptionResolutionResolvent`
   *  that fires replaces `m` with the shrunk resolvent, stopping early at `□`; returns the final clause. Shared
   *  by the few-units direct scan and the many-units indexed dispatch. */
  private def applyUnitDeletions(cands: collection.IndexedSeq[Clause], m0: Clause): Clause =
    var m: Clause = m0
    var k = 0
    while k < cands.length && !m.isEmpty do
      Subsumption.subsumptionResolutionResolvent(bank, trail, cands(k), m) match
        case Some(r) => stats.forwardUnitDeleted += 1; m = r
        case None => ()
      k += 1
    m

  /** Forward subsumption resolution, E-style ("char-2"): a stored clause SR-resolves `m` on literal `M` iff it
   *  *subsumes* `m` with `M` flipped. Flip each in turn ([[foreachFlipped]]), keep the non-unit subsumers
   *  (deduped by id), then apply `subsumptionResolutionResolvent` in **id order**, which is
   *  retrieval-independent. Slightly weaker than the complete rule, matching E's forward contextual
   *  simplify-reflect: a simplifier whose *other* literal also matches the resolved one is missed. */
  private def forwardSubsumptionResolveChar2(m0: Clause): Clause =
    var m: Clause = m0
    collectSubsumersOfFlipped(m, singleton = false, units = false, srCands)
    if srCands.nonEmpty then
      srCands.sortInPlaceBy(_.id)
      var k = 0
      while k < srCands.length && !m.isEmpty do
        Subsumption.subsumptionResolutionResolvent(bank, trail, srCands(k), m) match
          case Some(r) => stats.forwardSubsumptionResolved += 1; m = r
          case None => ()
        k += 1
    m

  // --- backward: subsumption / subsumption resolution -----------------------------------------------------

  /** Backward simplify the active set using `gc` (not yet active): delete each active clause `gc` subsumes, and
    * shrink each that `gc` subsumption-resolves a literal from (unit deletion if `gc` is a unit, general SR
    * otherwise). Shrunk clauses go to `emit` after the pass, never mid-iteration. `true` if one closes. */
  def backwardSubsume(gc: Clause)(emit: Clause => Boolean): Boolean =
    if backwardSubsumption then
      bwVictims.clear()
      active.subsumeeCandidates(gc) { d => if Subsumption.subsumes(bank, trail, gc, d) then bwVictims += d }
      var k = 0
      while k < bwVictims.length do
        stats.backwardSubsumed += 1
        active.remove(bwVictims(k))
        k += 1
    val gcUnit: Boolean = gc.size == 1
    shrunk.clear()
    if (if gcUnit then backwardUnitDeletion else backwardSubsumptionResolution) then
      seenIds.clear(); bwCands.clear()
      foreachFlipped(gc, singleton = false) { (query, _) =>
        active.subsumeeCandidates(query) { d => if seenIds.add(d.id) then bwCands += d } // `gc` is not active, so never itself
      }
      var k = 0
      while k < bwCands.length do
        val d: Clause = bwCands(k)
        Subsumption.subsumptionResolutionResolvent(bank, trail, gc, d) match
          case Some(r) =>
            if gcUnit then stats.backwardUnitDeleted += 1 else stats.backwardSubsumptionResolved += 1
            shrunk += r
            active.remove(d)
          case None => () // index false positive (feature-vector superset that does not actually resolve)
        k += 1
    emitAll(shrunk)(emit)

  /** Hand each collected replacement to `emit` in order, short-circuiting on `□`. */
  private def emitAll(replacements: mutable.ArrayBuffer[Clause])(emit: Clause => Boolean): Boolean =
    var k = 0
    while k < replacements.length do
      if emit(replacements(k)) then return true
      k += 1
    false

  // --- backward: demodulation -----------------------------------------------------------------------------

  /** When `gc` is a new positive unit equality, rewrite the active clauses with it: each rewritten clause is
    * removed from active and its replacement handed to `emit`. `true` on refutation. */
  def backwardDemodulate(gc: Clause)(emit: Clause => Boolean): Boolean =
    if !backwardDemodulationOn || !Demodulation.isPositiveUnitEquality(bank, gc) then return false
    val rs: Array[Demodulation.Rule] = Demodulation.rules(bank, gc).toArray
    if rs.isEmpty then return false
    seenIds.clear(); demodCands.clear()
    var ri = 0
    while ri < rs.length do
      active.demodulationTargets(rs(ri).lhs) { e => if seenIds.add(e.clause.id) then demodCands += e.clause }
      ri += 1
    var k = 0
    while k < demodCands.length do
      val c: Clause = demodCands(k)
      val r: Clause = Demodulation.normalForm(bank, trail, c, rs)
      if r.id != c.id then
        active.remove(c)
        if emit(r) then return true
      k += 1
    false
