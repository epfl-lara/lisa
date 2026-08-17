package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import scala.collection.mutable

import Core.*
import lisa.automation.superposition.index.*

/** How much each simplification fired during a saturation: observability, and what the ablations read.
  *
  * A counter is added by adding one field, and there is deliberately no `reset`: one `Simplifier` serves one
  * saturation, so a fresh record comes with it. */
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
  * of itself.
  *
  * Every retrieval goes through an index, which only narrows the candidate set: each is confirmed by the same
  * exact predicate (`Subsumption.subsumes`, or the matching inside `normalForm`). Redundancy a different
  * retrieval order would catch earlier is caught when the clause is later selected.
  *
  * The backward methods take an `emit` callback rather than returning their replacements, because a shrunk
  * clause has to reach the passive set, which this class does not own; collecting them instead would defer the
  * re-adds past the rewrite and removal they interleave with, shifting clause ids and the search trajectory.
  * `emit` returns `true` for "stop, `□` was derived", which they relay. */
final class Simplifier(bank: TermBank, trail: Trail, active: ActiveSet, opts: SearchOptions):
  import opts.*

  /** How much each simplification fired. One `Simplifier` serves one saturation, so these are never reset. */
  val stats: SimplificationStats = new SimplificationStats

  // --- reusable candidate buffers -------------------------------------------------------------------------
  //
  // Every retrieval here has to *collect* and then act, because mutating the feature-vector index during a
  // descent is refused (see [[FeatureVectorIndex]]). Fields, cleared at the point of use, so no append needs a
  // null check and nothing reallocates after the first given clause.
  //
  // Reuse is safe only because no two uses are live at once, which is worth checking, since `emit` re-enters
  // this class (`Discount.addPassive` calls [[condense]], and [[forward]] when `forwardSimplifyAtGeneration`):
  // [[shrunk]] and [[demodCands]] are iterated *across* `emit` calls and no forward path touches them, and
  // every other buffer is finished with before the first `emit`.

  private val unitCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty // forward unit deletion
  private val srCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty //   forward SR
  private val bwVictims: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty // backward subsumption
  private val bwCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty //   backward SR
  private val shrunk: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty //    backward replacements, emitted
  private val demodCands: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty // backward demodulation targets
  private val seenIds: IntOpenHashSet = new IntOpenHashSet() // dedup within one collection phase only

  /** Visit `use(query, i)` for each literal `i` of `c`, where `query` is a throwaway clause carrying `c` with
    * literal `i`'s polarity flipped (or, when `singleton`, just the single flipped literal `{¬Lᵢ}`).
    *
    * This is the query shape all three E-style "char-2" retrievals share, and stating it once is what makes
    * them recognisable as one idea: a stored clause subsumption-resolves `c` on `Lᵢ` exactly when it subsumes
    * `c` with `Lᵢ` flipped, and a unit deletes `Lᵢ` exactly when it subsumes the singleton `{¬Lᵢ}`. */
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

  /** Whether [[forward]] can do anything, so that a configuration with every forward simplification off does
    * not walk the active set per given for nothing.
    *
    * The gate lives here rather than in the loop because it must name every flag it guards. When the loop made
    * the decision it tested two of the three, so asking for subsumption resolution alone silently got nothing. */
  private val forwardEnabled: Boolean = forwardSubsumption || forwardUnitDeletion || forwardSubsumptionResolution

  /** The backward twin of [[forwardEnabled]] (same story, `Discount` gated on `backwardSubsumption ||
    * backwardUnitDeletion`). An over-approximation: which of the two subsumption-resolution flags applies
    * depends on whether the given is a unit, which is decided per call inside. */
  private val backwardEnabled: Boolean = backwardSubsumption || backwardUnitDeletion || backwardSubsumptionResolution

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

  /** Forward simplify `m` against the active set (active only: DISCOUNT does not forward-check passive). If
    * some active clause subsumes `m`, return `None`; otherwise apply subsumption resolution, returning the
    * possibly-shrunk clause or `Some(□)` if a resolution closed it. Forward subsumption asks the index an
    * *existence* question, so its `≤`-cone descent stops at the first verified subsumer; unit deletion
    * dispatches on the unit count ([[SearchOptions.forwardUnitDeletionIndexThreshold]]). */
  def forward(m0: Clause): Option[Clause] =
    if !forwardEnabled then return Some(m0)
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
        // subsumes the singleton `{¬K}`, so query the ≤-cone of each `{¬K}` (tiny for a singleton, hence cheap
        // and selective), verify with `subsumes`, and collect the units, deduped by id. Then one pass of
        // `subsumptionResolutionResolvent` over the candidates: exactly the unit scan restricted to the units
        // that can actually match (the rest give `None`), so the verdict is the same either way.
        seenIds.clear(); unitCands.clear()
        foreachFlipped(m, singleton = true) { (query, _) =>
          active.subsumerCandidates(query) { c =>
            if c.size == 1 && Subsumption.subsumes(bank, trail, c, query) && seenIds.add(c.id) then unitCands += c
          }
        }
        if unitCands.nonEmpty then
          m = applyUnitDeletions(unitCands, m)
          if m.isEmpty then return Some(m)
    if forwardSubsumptionResolution then
      m = forwardSubsumptionResolveChar2(m)
      if m.isEmpty then return Some(m)
    Some(m)

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
    seenIds.clear(); srCands.clear()
    foreachFlipped(m, singleton = false) { (query, _) =>
      active.subsumerCandidates(query) { c =>
        if c.size > 1 && Subsumption.subsumes(bank, trail, c, query) && seenIds.add(c.id) then srCands += c
      }
    }
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
  /** Backward subsumption collects the victims from the feature-vector index's `≥`-cone (verified by `subsumes`)
    * and then removes them. Backward **subsumption resolution**, and its unit-deletion special case, is E-style
    * (`RemoveContextualSRClauses`): `gc` SR-resolves `d` on literal `Lᵢ` iff `gc` with `Lᵢ` flipped subsumes `d`,
    * so the same index is queried with each one-literal-flipped `gc` ([[foreachFlipped]]), the `≥`-cones unioned
    * and deduped by id, and each candidate verified with `subsumptionResolutionResolvent`. */
  def backwardSubsume(gc: Clause)(emit: Clause => Boolean): Boolean =
    if !backwardEnabled then return false
    if backwardSubsumption then
      // `gc` is not yet in the active set, joining only after this and after backward demodulation, so it cannot
      // be among its own victims. Victims are collected and removed *after* the descent, which is what the index
      // requires of a retrieval callback.
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
        active.subsumeeCandidates(query) { d => if d.id != gc.id && seenIds.add(d.id) then bwCands += d }
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
    * removed from active and its replacement handed to `emit`. `true` on refutation.
    *
    * The demod-subterm index is queried with each of `gc`'s rule left sides to collect the candidate clauses (a
    * superset, since an instance subterm is among the unification candidates); each is then normal-formed
    * against `gc`'s rules, which verifies by matching, and replaced if it changed. */
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
