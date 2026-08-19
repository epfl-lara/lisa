package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.{Int2IntOpenHashMap, Int2ObjectOpenHashMap}

import scala.collection.mutable

import Core.*
import lisa.automation.superposition.index.*

/** The processed clauses and the structures that index them (five fingerprint indices, the demodulator tree,
  * the feature-vector index, and the unit sublist) each holding the same clauses under a different structure. The
  * buffer is the main one. */
final class ActiveSet(bank: TermBank, trail: Trail, initial: Seq[Clause], opts: SearchOptions):
  import opts.*

  // Which shadows are maintained at all is decided by the derived switches on [[SearchOptions]]
  // (`forwardDemodulationOn`, `indexedSuperposition`, `indexedSubsumption`, …), imported above: each is the
  // relevant inference being on *and* its indexing flag.

  // --- the authoritative store ----------------------------------------------------------------------------

  private val buffer: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty
  // clause id to its position in `buffer`, so removal is O(1) rather than a scan, which makes backward
  // simplification O(|active|) instead of O(|active|²). `-1` means absent.
  private val slot: Int2IntOpenHashMap = { val m = new Int2IntOpenHashMap(); m.defaultReturnValue(-1); m }
  private var _peakSize: Int = 0

  // --- the shadows ----------------------------------------------------------------------------------------

  private val intoIndex: FingerprintIndex[IntoEntry] = new FingerprintIndex(bank) // superposition: targets
  private val fromIndex: FingerprintIndex[FromEntry] = new FingerprintIndex(bank) // superposition: sources
  private val posLitIndex: FingerprintIndex[ResolutionEntry] = new FingerprintIndex(bank) // resolution
  private val negLitIndex: FingerprintIndex[ResolutionEntry] = new FingerprintIndex(bank) // resolution
  private val demodSubtermIndex: FingerprintIndex[IntoEntry] = new FingerprintIndex(bank) // backward demodulation
  private val demodTree: DiscriminationTree[Demodulation.Rule] = new DiscriminationTree(bank, trail) // forward demodulation
  private val units: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty // forward unit deletion

  /** The rules [[add]] inserted into [[demodTree]], by source clause id, so that [[remove]] takes out exactly
    * those rather than re-deriving them. Re-derivation would call `order.orient` and so reproduce the inserted
    * rules only while the ordering is unchanged; a rule re-derived with a different left side would descend a
    * different path, find nothing, and leave the real entry behind. */
  private val treeRulesOf: Int2ObjectOpenHashMap[List[Demodulation.Rule]] = new Int2ObjectOpenHashMap()

  /** The feature permutation adapts to the problem, so this needs the initial clauses, which is why they are a
    * constructor parameter. `null` when no simplification queries it. */
  private val subsumptionIndex: FeatureVectorIndex =
    if subsumptionEnabled then new FeatureVectorIndex(bank, Permutation.build(bank, initial)) else null

  /** How many clauses are active. */
  def size: Int = buffer.length
  def peakSize: Int = _peakSize

  /** The active unit clauses, as a small sublist so unit deletion needn't scan everything (units are few).
    * Maintained only when [[SearchOptions.subsumptionEnabled]]. */
  def unitClauses: collection.IndexedSeq[Clause] = units


  /** Add `c` to the active set and to every shadow. `c` must already have been activated (its literal
    * selection computed), since the superposition and resolution indices key on the *selected* literals. */
  def add(c: Clause): Unit =
    slot.put(c.id, buffer.length) // record its slot before appending (`c` lands at `buffer.length`)
    buffer += c
    if buffer.length > _peakSize then _peakSize = buffer.length
    if forwardDemodulationOn && Demodulation.isPositiveUnitEquality(bank, c) then
      val rules = Demodulation.rules(bank, c)
      rules.foreach(r => demodTree.insert(r.lhs, r))
      if rules.nonEmpty then treeRulesOf.put(c.id, rules) // exactly what `removeDemodulatorsOf` must undo
    if superpositionOn then updateSuperpositionEntries(c, add = true)
    updateResolutionEntries(c, add = true) // ordinary resolution always runs, so its indices are unconditional
    if subsumptionEnabled then
      subsumptionIndex.insert(c)
      if c.size == 1 then units += c
    if backwardDemodulationOn then updateDemodSubterms(c, add = true)

  /** Remove `c` from the active set and every shadow, or do nothing at all if `c` is not active: the shadows
    * hold entries for exactly the buffered clauses, so absence from the buffer settles both halves. */
  def remove(c: Clause): Unit =
    val i: Int = slot.get(c.id)
    if i >= 0 then
      detach(c)
      removeAtInBuffer(i)

  // --- retrieval (each a thin wrapper over the owning shadow) ---------------------------------------------

  /** Superposition *targets*: entries whose subterm may unify with the rewriting LHS `l`. */
  def intoCandidates(l: Term)(visit: IntoEntry => Unit): Unit = intoIndex.retrieveUnifiable(l)(visit)

  /** Superposition *sources*: equations whose usable side may unify with the subterm `u`. */
  def fromCandidates(u: Term)(visit: FromEntry => Unit): Unit = fromIndex.retrieveUnifiable(u)(visit)

  /** Resolution partners for a literal: the *opposite*-polarity index is queried, so every candidate is
    * already complementary. */
  def resolutionPartners(positive: Boolean, atom: Term)(visit: ResolutionEntry => Unit): Unit =
    (if positive then negLitIndex else posLitIndex).retrieveUnifiable(atom)(visit)

  /** Clauses with a rewritable subterm that a new demodulator's LHS may reduce (a superset, verified by the
    * matching inside `normalForm`). */
  def demodulationTargets(lhs: Term)(visit: IntoEntry => Unit): Unit = demodSubtermIndex.retrieveUnifiable(lhs)(visit)

  /** Whether some stored clause satisfying `pred` subsumes-cone-dominates `q`, short-circuiting at the first. */
  def existsSubsumer(q: ClauseBody)(pred: Clause => Boolean): Boolean = subsumptionIndex.existsForwardCandidate(q)(pred)

  /** Candidate subsumers of `q` (its `≤`-cone). The callback must only *collect*: mutating the index during
    * the descent is refused (see [[FeatureVectorIndex]]). */
  def subsumerCandidates(q: ClauseBody)(visit: Clause => Unit): Unit = subsumptionIndex.forwardCandidates(q)(visit)

  /** Candidate subsumees of `q` (its `≥`-cone). Same collect-only rule as [[subsumerCandidates]]. */
  def subsumeeCandidates(q: ClauseBody)(visit: Clause => Unit): Unit = subsumptionIndex.backwardCandidates(q)(visit)

  /** Normal-form `c` against the active demodulators. Returns `c` itself when demodulation is off or nothing
    * rewrites (`normalFormIndexed` short-circuits on an empty tree). */
  def demodulate(c: Clause): Clause =
    if !forwardDemodulationOn then c
    else Demodulation.normalFormIndexed(bank, trail, c, demodTree)

  // --- internals ------------------------------------------------------------------------------------------

  /** Swap-with-last + truncate, patching the moved element's recorded slot. `buffer` is unordered, so the
    * reorder is harmless. */
  private def removeAtInBuffer(i: Int): Unit =
    val last: Int = buffer.length - 1
    slot.remove(buffer(i).id)
    if i != last then
      val moved: Clause = buffer(last)
      buffer(i) = moved
      slot.put(moved.id, i)
    buffer.remove(last)

  /** Drop `c` from every shadow. The exact inverse of the shadow half of [[add]]. */
  private def detach(c: Clause): Unit =
    require(c.selected != null, s"ActiveSet.remove: clause ${c.id} was never activated, so its index entries " +
      "cannot be re-derived (they key on the selected literals)")
    if forwardDemodulationOn && Demodulation.isPositiveUnitEquality(bank, c) then removeDemodulatorsOf(c)
    if superpositionOn then updateSuperpositionEntries(c, add = false)
    updateResolutionEntries(c, add = false)
    if subsumptionEnabled then
      subsumptionIndex.remove(c)
      if c.size == 1 then removeUnit(c) // guarded exactly as `add` is: only units were ever appended
    if backwardDemodulationOn then updateDemodSubterms(c, add = false)

  /** Index (`add`) or de-index (`!add`, matched by value equality) `c`'s superposition terms: every
    * non-variable subterm of its selected literals in the into-index, and each rewrite it offers in the
    * from-index. The into-entries are re-derived by the same subterm walk on both sides; the rewrites come from
    * [[Core.Clause.rewriteSources]], which memoises them, so removal takes out exactly the entries insertion
    * put in. */
  private def updateSuperpositionEntries(c: Clause, add: Boolean): Unit =
    val sel: Array[Int] = c.selected
    var k = 0
    while k < sel.length do
      val iLit: Int = sel(k)
      Superposition.foreachSubterm(bank, bank.atomOf(c.literals(iLit))) { (u, path) =>
        val e = new IntoEntry(c, iLit, path.toIntArray)
        if add then intoIndex.insert(u, e) else intoIndex.remove(u, e); false
      }
      k += 1
    val sources: Array[RewriteSource] = c.rewriteSources(bank)
    var s = 0
    while s < sources.length do
      val src: RewriteSource = sources(s)
      val e = new FromEntry(c, src.lit, src.side)
      if add then fromIndex.insert(src.lhs, e) else fromIndex.remove(src.lhs, e)
      s += 1

  /** Index (`add`) or de-index (`!add`) `c`'s selected non-equality literal atoms: positive atoms in the
    * positive index, negative in the negative one, so a query fetches only complementary candidates. */
  private def updateResolutionEntries(c: Clause, add: Boolean): Unit =
    val sel: Array[Int] = c.selected
    var k = 0
    while k < sel.length do
      val iLit: Int = sel(k)
      val lit: Literal = c.literals(iLit)
      if !bank.isEquality(lit) then
        val idx = if bank.isPositive(lit) then posLitIndex else negLitIndex
        val e = new ResolutionEntry(c, iLit)
        if add then idx.insert(bank.atomOf(lit), e) else idx.remove(bank.atomOf(lit), e)
      k += 1

  /** Index (`add`) or de-index (`!add`) every rewritable subterm of *every* literal of `c`, since demodulation
    * rewrites any of them, not only the selected ones. */
  private def updateDemodSubterms(c: Clause, add: Boolean): Unit =
    var iLit = 0
    while iLit < c.literals.length do
      val li: Int = iLit
      Superposition.foreachSubterm(bank, bank.atomOf(c.literals(li))) { (u, path) =>
        val e = new IntoEntry(c, li, path.toIntArray)
        if add then demodSubtermIndex.insert(u, e) else demodSubtermIndex.remove(u, e); false
      }
      iLit += 1

  /** Remove the unit clause `c` from the unit sublist; swap-with-last. A no-op if absent, though the caller's
    * guard means the only absent case is a unit that was never added. */
  private def removeUnit(c: Clause): Unit =
    var i = 0
    while i < units.length do
      if units(i).id == c.id then
        units(i) = units(units.length - 1)
        units.remove(units.length - 1)
        return
      i += 1

  /** Drop the demodulators whose source is the (removed) clause `c` from the discrimination tree: exactly the
    * rules [[add]] recorded, never re-derived (see [[treeRulesOf]]). */
  private def removeDemodulatorsOf(c: Clause): Unit =
    var xs = treeRulesOf.remove(c.id)
    if xs != null then while xs.nonEmpty do { demodTree.remove(xs.head.lhs, xs.head); xs = xs.tail }
