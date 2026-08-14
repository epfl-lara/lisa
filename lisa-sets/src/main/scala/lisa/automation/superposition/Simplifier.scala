package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import scala.collection.mutable

import Core.*

/** How much each simplification fired during a saturation: observability, and what the ablations read. */
final class SimplificationStats:
  var forwardSubsumed: Int = 0
  var backwardSubsumed: Int = 0
  var forwardUnitDeleted: Int = 0
  var backwardUnitDeleted: Int = 0
  var forwardSubsumptionResolved: Int = 0 // multi-literal-side forward SR
  var backwardSubsumptionResolved: Int = 0
  var condensed: Int = 0

  def reset(): Unit =
    forwardSubsumed = 0; backwardSubsumed = 0; forwardUnitDeleted = 0; backwardUnitDeleted = 0
    forwardSubsumptionResolved = 0; backwardSubsumptionResolved = 0; condensed = 0

/**
 * Every **simplification** (redundancy) step of the DISCOUNT loop, in both directions and in both the indexed
 * and scanning variants. Generating inferences live elsewhere; what is here only ever *deletes* clauses or
 * replaces them by something shorter that entails them.
 *
 *   - **forward** ([[forward]]) discards or shrinks the clause being added or selected, using the active set:
 *     subsumption, unit deletion, and general subsumption resolution (on by default; see
 *     [[SearchOptions.forwardSubsumptionResolution]] for the ablation each default came from).
 *   - **backward** ([[backwardSubsume]], [[backwardDemodulate]]) deletes or shrinks *active* clauses using the
 *     given, run before the given itself joins the active set so it never simplifies itself.
 *   - **clause-local** ([[condense]]) replaces a clause by an equivalent shorter factor of itself.
 *
 * Each direction has an indexed path and a linear-scan path, kept side by side deliberately: they are the A/B
 * apparatus that makes the index-correctness claims testable (each index is a candidate *filter* confirmed by
 * the same exact `Subsumption` predicate, so both paths must reach the same verdict). `DiscountTest` compares
 * them on curated clause sets.
 *
 * '''Why the backward methods take an `emit` callback rather than returning their replacements.''' A shrunk
 * clause has to reach the passive set, which this class does not own. Returning a list would work for
 * subsumption resolution, whose replacements are already collected and added in a batch, but *not* for
 * backward demodulation, which interleaves rewrite, removal and re-add per clause. Deferring those re-adds
 * would move the `canonicalize` calls inside them, shifting clause ids and hence the whole search trajectory.
 * The callback keeps the interleaving exactly as it was. It returns `Some(□)` when the clause it was handed is
 * (or simplifies to) the empty clause, which short-circuits the caller.
 *
 * Nothing here needs a proof obligation: subsumption *deletion* never enters `□`'s [[Justification]] DAG at
 * all, and every shrunk clause is an ordinary resolvent or factor built by [[Inference]], so it reconstructs
 * with no dedicated machinery.
 */
final class Simplifier(bank: TermBank, trail: Trail, active: ActiveSet, opts: SearchOptions):
  import opts.*

  val stats: SimplificationStats = new SimplificationStats

  private val backwardDemodulationOn: Boolean = equality && backwardDemodulation
  private val indexedBackwardDemod: Boolean = backwardDemodulationOn && demodulationIndexing

  /**
   * Whether [[forward]] can do anything at all: the early-out for a configuration with every forward
   * simplification off, where `forwardScan` would otherwise walk the whole active set per given doing nothing.
   *
   * '''Why the decision lives here.''' The loop used to make it, gating its `forward` call on
   * `forwardSubsumption || forwardUnitDeletion` while this class runs subsumption resolution on its own flag
   * inside. Those two conditions are not the same, so a configuration asking for subsumption resolution *alone*
   * (`SearchOptions(forwardSubsumption = false, forwardUnitDeletion = false, forwardSubsumptionResolution =
   * true)`) got none of it, silently: three knobs documented as independent axes, one of which could never fire.
   * A gate can only stay in step with the flags it guards if it lives beside them, so the loop now calls
   * [[forward]] unconditionally and this owns the question.
   */
  private val forwardEnabled: Boolean = forwardSubsumption || forwardUnitDeletion || forwardSubsumptionResolution

  /** The backward twin of [[forwardEnabled]] (same story, `Discount` gated on `backwardSubsumption ||
    * backwardUnitDeletion`). An over-approximation: which of the two subsumption-resolution flags applies
    * depends on whether the given is a unit, which is decided per call inside. */
  private val backwardEnabled: Boolean = backwardSubsumption || backwardUnitDeletion || backwardSubsumptionResolution

  // --- clause-local ---------------------------------------------------------------------------------

  /** Replace `c` by an equivalent shorter factor of itself, if one exists and [[SearchOptions.condensation]]
    * is on. Clause-local: no active-set scan, applied once at creation. Cannot produce `□` or a tautology. */
  def condense(c: Clause): Clause =
    if !condensation then c
    else
      val cd: Clause = Subsumption.condense(bank, trail, c)
      if cd ne c then stats.condensed += 1
      cd

  // --- forward --------------------------------------------------------------------------------------

  /** Forward simplify `m` against the active set (active only, since DISCOUNT does not forward-check passive): if
    * some active clause subsumes `m`, return `None` (discard it); otherwise apply subsumption resolution by
    * active clauses (unit deletion for unit sides, general SR for longer ones), returning the possibly-shrunk
    * clause, or `Some(□)` if a resolution closed it. */
  def forward(m0: Clause): Option[Clause] =
    if !forwardEnabled then Some(m0)
    else if active.indexedSubsumption then forwardIndexed(m0) else forwardScan(m0)

  /** Indexed forward simplification: forward subsumption via the feature-vector index
   *  ([[FeatureVectorIndex.existsForwardCandidate]], stopping the ≤-cone descent at the first verified
   *  subsumer); unit deletion via the active-unit scan / `{¬K}` index dispatch; general subsumption resolution
   *  via [[forwardSubsumptionResolveChar2]] over the same feature-vector index. Same verdict as
   *  [[forwardScan]]: each index is a candidate filter over the same `Subsumption.subsumes`, and the residual
   *  redundancy a different scan order might catch is caught when the clause is later selected. */
  private def forwardIndexed(m0: Clause): Option[Clause] =
    var m: Clause = m0
    if forwardSubsumption then
      // An existence question, so the ≤-cone descent short-circuits at the first verified subsumer, matching
      // `forwardScan`, which returns as soon as it finds one.
      if active.existsSubsumer(m)(c => Subsumption.subsumes(bank, trail, c, m)) then
        stats.forwardSubsumed += 1
        return None
    if forwardUnitDeletion then
      if active.unitClauses.length <= forwardUnitDeletionIndexThreshold then
        // Few units: scan the active-unit sublist directly (near-zero fixed overhead).
        m = applyUnitDeletions(active.unitClauses, m)
        if m.isEmpty then return Some(m)
      else
        // Many units: gather the candidate units via the index. A unit deletes a literal `K` of `m` iff it subsumes
        // the singleton `{¬K}`, so for each literal we query the ≤-cone of `{¬K}` (tiny for a singleton, hence
        // cheap and selective), verify with `subsumes`, and collect the units (deduped by id). Then one pass of
        // `subsumptionResolutionResolvent` over the candidates, exactly the unit scan restricted to units that
        // can actually match (the rest give `None`), so the verdict is unchanged.
        val seen = new IntOpenHashSet()
        var cands: mutable.ArrayBuffer[Clause] = null
        var li = 0
        while li < m.literals.length do
          val flipped: Clause = bank.mkQueryClause(Array(bank.negate(m.literals(li)))) // singleton {¬K}
          active.subsumerCandidates(flipped) { c =>
            if c.size == 1 && Subsumption.subsumes(bank, trail, c, flipped) && seen.add(c.id) then
              if cands == null then cands = mutable.ArrayBuffer.empty
              cands += c
          }
          li += 1
        if cands != null then
          m = applyUnitDeletions(cands, m)
          if m.isEmpty then return Some(m)
    if forwardSubsumptionResolution then
      m = forwardSubsumptionResolveChar2(m, useIndex = true)
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

  /** Linear forward simplification (the pre-index scan; kept behind `subsumptionIndexing` for A/B). One pass over
   *  the active set: subsumed ⇒ discard; else subsumption-resolution (unit deletion for unit sides, general SR for
   *  longer ones) shrinks `m` and the scan continues with the shorter clause. */
  private def forwardScan(m0: Clause): Option[Clause] =
    var m: Clause = m0
    var i = 0
    while i < active.size do
      val c: Clause = active(i)
      if forwardSubsumption && Subsumption.subsumes(bank, trail, c, m) then
        stats.forwardSubsumed += 1
        return None // subsumed: discard `m`
      // resolution arm runs only on clauses `c` does not subsume; gated by side size + flag
      if c.size == 1 && forwardUnitDeletion then // unit deletion here; general SR is done char-2 after the loop
        Subsumption.subsumptionResolutionResolvent(bank, trail, c, m) match
          case Some(r) => // `r` is the canonical shrunk clause (it entails `m`)
            stats.forwardUnitDeleted += 1
            if r.isEmpty then return Some(r) // resolution closed the clause
            m = r // continue the scan with the shrunk clause
          case None => ()
      i += 1
    if forwardSubsumptionResolution then
      m = forwardSubsumptionResolveChar2(m, useIndex = false)
      if m.isEmpty then return Some(m)
    Some(m)

  /** Forward subsumption resolution, E-style ("char-2"): a stored clause SR-resolves `m` by removing a literal `M`
   *  iff it *subsumes* `m` with `M` flipped. So for each literal we flip it and find the active clauses subsuming
   *  the flipped `m`, via the feature-vector index when `useIndex` and a linear active scan otherwise, keep the
   *  non-unit ones (deduped by id), then apply `subsumptionResolutionResolvent` in **id order** (retrieval-
   *  independent, so the indexed and scanned paths shrink identically), returning `□` if a resolvent closes `m`.
   *  This is slightly weaker than the complete rule: a simplifier whose *other* literal also matches the resolved
   *  literal is missed (the query-side flip cannot see it), matching E's forward contextual simplify-reflect; both
   *  paths do it, so the indexed-vs-scan A/B stays exact. */
  private def forwardSubsumptionResolveChar2(m0: Clause, useIndex: Boolean): Clause =
    var m: Clause = m0
    val seen = new IntOpenHashSet()
    var cands: mutable.ArrayBuffer[Clause] = null
    def consider(c: Clause, query: Clause): Unit =
      if c.size > 1 && Subsumption.subsumes(bank, trail, c, query) && seen.add(c.id) then
        if cands == null then cands = mutable.ArrayBuffer.empty
        cands += c
    var li = 0
    while li < m.literals.length do
      val lits: Array[Literal] = m.literals.clone(); lits(li) = bank.negate(lits(li))
      val query: Clause = bank.mkQueryClause(lits) // `m` with literal li flipped
      if useIndex then active.subsumerCandidates(query)(consider(_, query))
      else { var i = 0; while i < active.size do { consider(active(i), query); i += 1 } }
      li += 1
    if cands != null then
      val sorted: mutable.ArrayBuffer[Clause] = cands.sortInPlaceBy(_.id)
      var k = 0
      while k < sorted.length && !m.isEmpty do
        Subsumption.subsumptionResolutionResolvent(bank, trail, sorted(k), m) match
          case Some(r) => stats.forwardSubsumptionResolved += 1; m = r
          case None => ()
        k += 1
    m

  // --- backward: subsumption / subsumption resolution -------------------------------------------------

  /** Backward simplify the active set using `gc` (not yet active): delete each active clause `gc` subsumes, and
    * shrink each that `gc` subsumption-resolves a literal from (unit deletion if `gc` is a unit, general SR
    * otherwise). Shrunk clauses go to `emit` after the pass, never mid-iteration. `Some(□)` if one closes. */
  def backwardSubsume(gc: Clause)(emit: Clause => Option[Clause]): Option[Clause] =
    if !backwardEnabled then None
    else if active.indexedSubsumption then backwardIndexed(gc)(emit) else backwardScan(gc)(emit)

  /** Indexed backward simplification: backward subsumption collects the victims via the feature-vector index
   *  (verified by `subsumes`) then removes them. Backward **subsumption resolution** (and its unit-deletion
   *  special case) is also indexed, E-style (`RemoveContextualSRClauses`): `gc` SR-resolves `d` on literal `Lᵢ`
   *  iff `gc` with `Lᵢ` flipped subsumes `d`, so we query the *same* index with each one-literal-flipped `gc`
   *  (their ≥-cones = candidate subsumees), union + dedup by id, and verify each with
   *  `subsumptionResolutionResolvent`. Same verdict as [[backwardScan]]. */
  private def backwardIndexed(gc: Clause)(emit: Clause => Option[Clause]): Option[Clause] =
    if backwardSubsumption then
      var victims: mutable.ArrayBuffer[Clause] = null // collect first (don't mutate `active`/index mid-descent)
      // `gc` is not yet in the active set, joining only after this and after backward demodulation, so it cannot
      // be among its own victims. Victims are removed *after* the descent, which is what the index requires of
      // a retrieval callback.
      active.subsumeeCandidates(gc) { d =>
        if Subsumption.subsumes(bank, trail, gc, d) then
          if victims == null then victims = mutable.ArrayBuffer.empty
          victims += d
      }
      if victims != null then
        var k = 0
        while k < victims.length do
          stats.backwardSubsumed += 1
          active.remove(victims(k))
          k += 1
    val gcUnit: Boolean = gc.size == 1
    var shrunk: mutable.ArrayBuffer[Clause] = null
    if (if gcUnit then backwardUnitDeletion else backwardSubsumptionResolution) then
      val seen = new IntOpenHashSet()
      var cands: mutable.ArrayBuffer[Clause] = null
      var i = 0
      while i < gc.literals.length do
        val lits: Array[Literal] = gc.literals.clone(); lits(i) = bank.negate(lits(i))
        val flipped: Clause = bank.mkQueryClause(lits) // `gc` with literal i flipped
        active.subsumeeCandidates(flipped) { d =>
          if d.id != gc.id && seen.add(d.id) then
            if cands == null then cands = mutable.ArrayBuffer.empty
            cands += d
        }
        i += 1
      if cands != null then
        var k = 0
        while k < cands.length do
          val d: Clause = cands(k)
          Subsumption.subsumptionResolutionResolvent(bank, trail, gc, d) match
            case Some(r) =>
              if gcUnit then stats.backwardUnitDeleted += 1 else stats.backwardSubsumptionResolved += 1
              if shrunk == null then shrunk = mutable.ArrayBuffer.empty
              shrunk += r
              active.remove(d)
            case None => () // index false positive (feature-vector superset that does not actually resolve)
          k += 1
    emitAll(shrunk)(emit)

  /** Linear backward simplification (the pre-index scan; kept behind `subsumptionIndexing` for A/B). One pass:
   *  delete each active clause `gc` subsumes, shrink each it subsumption-resolves; shrunk clauses emitted after. */
  private def backwardScan(gc: Clause)(emit: Clause => Option[Clause]): Option[Clause] =
    val gcUnit: Boolean = gc.size == 1
    val srOn: Boolean = if gcUnit then backwardUnitDeletion else backwardSubsumptionResolution
    var shrunk: mutable.ArrayBuffer[Clause] = null // emitted after the scan (lazily allocated)
    var i = 0
    while i < active.size do
      val m: Clause = active(i)
      var removed = false
      if backwardSubsumption && Subsumption.subsumes(bank, trail, gc, m) then
        stats.backwardSubsumed += 1
        removed = true
      else if srOn then
        Subsumption.subsumptionResolutionResolvent(bank, trail, gc, m) match
          case Some(r) =>
            if gcUnit then stats.backwardUnitDeleted += 1 else stats.backwardSubsumptionResolved += 1
            if shrunk == null then shrunk = mutable.ArrayBuffer.empty
            shrunk += r
            removed = true
          case None => ()
      if removed then
        active.removeAt(i) // swap-with-last; re-check the swapped-in element (don't advance)
      else i += 1
    emitAll(shrunk)(emit)

  /** Hand each collected replacement to `emit` in order, short-circuiting on `□`. */
  private def emitAll(shrunk: mutable.ArrayBuffer[Clause])(emit: Clause => Option[Clause]): Option[Clause] =
    if shrunk == null then None
    else
      var k = 0
      while k < shrunk.length do
        emit(shrunk(k)) match
          case Some(empty) => return Some(empty)
          case None => ()
        k += 1
      None

  // --- backward: demodulation -------------------------------------------------------------------------

  /** When `gc` is a new positive unit equality, rewrite the active clauses with it: each rewritten clause is
    * removed from active and its replacement handed to `emit`. `Some(□)` on refutation. */
  def backwardDemodulate(gc: Clause)(emit: Clause => Option[Clause]): Option[Clause] =
    if !backwardDemodulationOn || !Demodulation.isPositiveUnitEquality(bank, gc) then None
    else if indexedBackwardDemod then backwardDemodulateIndexed(gc)(emit)
    else
      var pairs = Demodulation.backwardDemodulate(bank, trail, bank.order, gc, active.clauses)
      while pairs.nonEmpty do
        val (removed, replacement) = pairs.head
        active.remove(removed)
        emit(replacement) match
          case Some(empty) => return Some(empty)
          case None => ()
        pairs = pairs.tail
      None

  /** Indexed backward demodulation: query the demod-subterm index with each of `gc`'s rule LHSs to collect the
   *  candidate active clauses (a superset, since an instance subterm is among the unification candidates), then
   *  normal-form each against `gc`'s rules (which verifies by matching) and replace the ones that change.
   *  Rewrites the same set of clauses as the scan; only the order (hence ids) differs. `Some(□)` on refutation. */
  private def backwardDemodulateIndexed(gc: Clause)(emit: Clause => Option[Clause]): Option[Clause] =
    val rs: Array[Demodulation.Rule] = Demodulation.rules(bank, bank.order, gc).toArray
    if rs.isEmpty then None
    else
      val seen: IntOpenHashSet = new IntOpenHashSet() // distinct candidate clause ids
      val candidates: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty
      var ri = 0
      while ri < rs.length do
        active.demodulationTargets(rs(ri).lhs) { e => if seen.add(e.clause.id) then candidates += e.clause }
        ri += 1
      var k = 0
      while k < candidates.length do
        val c: Clause = candidates(k)
        val r: Clause = Demodulation.normalForm(bank, trail, bank.order, c, rs)
        if r.id != c.id then
          active.remove(c)
          emit(r) match
            case Some(empty) => return Some(empty)
            case None => ()
        k += 1
      None
