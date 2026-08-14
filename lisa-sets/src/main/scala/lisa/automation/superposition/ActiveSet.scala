package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.{Int2IntOpenHashMap, Int2ObjectOpenHashMap}

import scala.collection.mutable

import Core.*

/**
 * The **active** (processed) clause set, together with every auxiliary structure that shadows it.
 *
 * `clauses` is the single source of truth. Around it sit up to seven derived views, each holding a slice of
 * the same clauses under a different key so that one query is fast:
 *
 *   - `activeDemodulators` / `demodTree`: the positive unit equalities as rewrite rules, keyed by LHS;
 *   - `intoIndex`: every non-variable subterm of *selected* literals (superposition targets);
 *   - `fromIndex`: the usable maximal sides of selected positive equalities (superposition sources);
 *   - `posLitIndex` / `negLitIndex`: selected non-equality atoms, split by polarity (resolution partners);
 *   - `subsumptionIndex`: whole clauses, keyed by feature vector (subsumption cones);
 *   - `activeUnits`: the unit clauses (unit deletion);
 *   - `demodSubtermIndex`: every rewritable subterm of *all* literals (backward demodulation).
 *
 * None is authoritative and all must be kept in step: a clause that leaves `clauses` but lingers in a shadow
 * is not *unsound*, being still a validly derived consequence with an intact `Justification`, but it
 * defeats the deletion that removed it, keeps being offered as an inference partner, and can never be
 * collected. Nothing fails; the search just quietly degrades.
 *
 * That obligation used to be a comment honoured at four separate call sites in the loop. Here it is a class
 * boundary: [[add]] and [[remove]] are the only doors in and out, and each one touches every structure.
 *
 * '''Removal re-derives its entries.''' There are no back-pointers from a clause to its (many) index entries:
 * a clause with three selected literals of five subterms each owns fifteen `intoIndex` entries. Removal walks
 * the clause again and deletes by value equality, so it needs every such derivation to answer the same way it
 * did on insertion. Each one is arranged so that it does, without appeal to when it runs:
 *
 *   - the subterm walks (`intoIndex`, `demodSubtermIndex`) and the literal reads (`posLitIndex`/`negLitIndex`)
 *     depend only on the literals and on `Clause.selected`, which is computed once and cached, as [[detach]]
 *     asserts it is present;
 *   - the from-sides depend on the term ordering, so they are not re-derived at all: both sides read the
 *     clause's cached [[Core.Clause.fromSides]];
 *   - the demodulator rules likewise: [[add]] records what it inserted (see [[treeRulesOf]]) and [[remove]]
 *     takes out exactly those;
 *   - the subsumption index recomputes a feature vector, over a [[Permutation]] frozen at [[reset]].
 *
 * So no part of removal rests on the ordering having stayed put, even though it has (the precedence and weights
 * are assigned before the loop starts and not touched again).
 */
final class ActiveSet(bank: TermBank, trail: Trail, opts: SearchOptions):
  import opts.*

  /** Which shadows are maintained at all. Each is the relevant inference being on *and* its indexing flag. */
  private val forwardDemodulationOn: Boolean = equality && forwardDemodulation
  private val backwardDemodulationOn: Boolean = equality && backwardDemodulation
  private val indexedSuperposition: Boolean = equality && superposition && fingerprintIndexing
  private val indexedResolution: Boolean = fingerprintIndexing
  private val indexedForwardDemod: Boolean = forwardDemodulationOn && demodulationIndexing
  private val indexedBackwardDemod: Boolean = backwardDemodulationOn && demodulationIndexing

  /** Whether subsumption queries go through the feature-vector index rather than a linear scan. Read by the
    * loop to pick between its indexed and scanning simplification paths. */
  val indexedSubsumption: Boolean = subsumptionIndexing && (forwardSubsumption || backwardSubsumption)

  // --- the authoritative store ---------------------------------------------------------------------

  private val buffer: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty
  // clause id → its index in `buffer`, so a clause is located for removal in O(1) (Vampire's `DHMap`
  // approach) instead of a linear id-scan, making backward simplification O(|active|) not O(|active|²).
  // Sized to |active| (not all clauses), so its footprint tracks the small processed set. `-1` = absent.
  private val slot: Int2IntOpenHashMap = { val m = new Int2IntOpenHashMap(); m.defaultReturnValue(-1); m }
  private var _peakSize: Int = 0

  // --- the shadows ---------------------------------------------------------------------------------

  private val intoIndex: FingerprintIndex[IntoEntry] = new FingerprintIndex(bank)
  private val fromIndex: FingerprintIndex[FromEntry] = new FingerprintIndex(bank)
  private val posLitIndex: FingerprintIndex[ResolutionEntry] = new FingerprintIndex(bank)
  private val negLitIndex: FingerprintIndex[ResolutionEntry] = new FingerprintIndex(bank)
  private val demodSubtermIndex: FingerprintIndex[IntoEntry] = new FingerprintIndex(bank)
  private val demodTree: DiscriminationTree = new DiscriminationTree(bank, trail)
  private val activeDemodulators: mutable.ArrayBuffer[Demodulation.Rule] = mutable.ArrayBuffer.empty
  private val units: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty

  /** The rules [[add]] inserted into [[demodTree]], by source clause id, so [[remove]] can take out exactly
    * those instead of re-deriving them (an `orient` and a `varsOf` per removal).
    *
    * It also stops the removal from depending on an unstated invariant. `Demodulation.rules` calls
    * `order.orient`, so re-derivation only reproduces the inserted rules while the ordering is unchanged. That
    * holds today, since the precedence and weights are fixed before each saturation and `reset` clears this
    * map, but nothing in the removal path said so or would fail loudly if it stopped holding: a re-derived
    * rule with a different `lhs` descends a different tree path, finds nothing, and leaves the real entry
    * behind. Recording what was inserted removes the question.
    *
    * Populated only when [[indexedForwardDemod]]; the linear [[activeDemodulators]] path finds its own
    * entries by source id. */
  private val treeRulesOf: Int2ObjectOpenHashMap[List[Demodulation.Rule]] = new Int2ObjectOpenHashMap()
  // Built fresh per saturation: the feature permutation adapts to that problem's clauses.
  private var subsumptionIndex: FeatureVectorIndex = null

  // --- storage view --------------------------------------------------------------------------------

  def size: Int = buffer.length
  def apply(i: Int): Clause = buffer(i)
  def isEmpty: Boolean = buffer.isEmpty
  def peakSize: Int = _peakSize

  /** The processed clauses, for the paths that genuinely iterate all of them (the linear scan variants kept
    * for A/B comparison, and backward demodulation's non-indexed arm). */
  def clauses: collection.IndexedSeq[Clause] = buffer

  /** The active unit clauses, as a small sublist so unit deletion needn't scan everything (units are few).
    * Maintained only when [[indexedSubsumption]]; the scanning path walks the whole set instead. */
  def unitClauses: collection.IndexedSeq[Clause] = units

  /** Drop everything and prepare for a fresh saturation over `initial` (whose signature shapes the
    * subsumption index's feature permutation). */
  def reset(initial: Seq[Clause]): Unit =
    buffer.clear(); slot.clear(); _peakSize = 0
    intoIndex.clear(); fromIndex.clear(); posLitIndex.clear(); negLitIndex.clear(); demodSubtermIndex.clear()
    demodTree.clear(); activeDemodulators.clear(); treeRulesOf.clear(); units.clear()
    if indexedSubsumption then subsumptionIndex = new FeatureVectorIndex(bank, Permutation.build(bank, initial))

  // --- the only two doors --------------------------------------------------------------------------

  /**
   * Add `c` to the active set and to every shadow. `c` must already have been activated (its literal
   * selection computed), since the superposition and resolution indices key on the *selected* literals.
   */
  def add(c: Clause): Unit =
    require(!c.isQuery, "ActiveSet.add: a query clause is a throwaway index key with a shared sentinel id; " +
      "storing it would alias every other query clause in `slot` and the lazy-deletion sets")
    slot.put(c.id, buffer.length) // record its slot before appending (`c` lands at `buffer.length`)
    buffer += c
    if buffer.length > _peakSize then _peakSize = buffer.length
    if forwardDemodulationOn && Demodulation.isPositiveUnitEquality(bank, c) then
      val rules = Demodulation.rules(bank, bank.order, c)
      if indexedForwardDemod then
        rules.foreach(demodTree.insert)
        if rules.nonEmpty then treeRulesOf.put(c.id, rules) // exactly what `removeDemodulatorsOf` must undo
      else activeDemodulators ++= rules
    if indexedSuperposition then updateSuperpositionEntries(c, add = true)
    if indexedResolution then updateResolutionEntries(c, add = true)
    if indexedSubsumption then
      subsumptionIndex.insert(c)
      if c.size == 1 then units += c
    if indexedBackwardDemod then updateDemodSubterms(c, add = true)

  /** Remove `c` from the active set and every shadow. A no-op on the buffer if `c` is not present. */
  def remove(c: Clause): Unit =
    detach(c)
    val i: Int = slot.get(c.id)
    if i >= 0 then removeAtInBuffer(i)

  /** Remove the clause at buffer position `i` (and its shadows). For the scanning backward pass, which
    * iterates by index and must not advance after a removal, since the swapped-in element takes slot `i`. */
  def removeAt(i: Int): Unit =
    detach(buffer(i))
    removeAtInBuffer(i)

  // --- retrieval (each a thin wrapper over the owning shadow) --------------------------------------

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
  def existsSubsumer(q: Clause)(pred: Clause => Boolean): Boolean = subsumptionIndex.existsForwardCandidate(q)(pred)

  /** Candidate subsumers of `q` (its `≤`-cone). The callback must only *collect*: mutating the index during
    * the descent is refused (see [[FeatureVectorIndex]]). */
  def subsumerCandidates(q: Clause)(visit: Clause => Unit): Unit = subsumptionIndex.forwardCandidates(q)(visit)

  /** Candidate subsumees of `q` (its `≥`-cone). Same collect-only rule as [[subsumerCandidates]]. */
  def subsumeeCandidates(q: Clause)(visit: Clause => Unit): Unit = subsumptionIndex.backwardCandidates(q)(visit)

  /** Normal-form `c` against the active demodulators, hiding the tree-vs-list dispatch. Returns `c` itself
    * when demodulation is off or nothing rewrites. */
  def demodulate(c: Clause): Clause =
    if !forwardDemodulationOn then c
    else if indexedForwardDemod then Demodulation.normalFormIndexed(bank, trail, bank.order, c, demodTree)
    else if activeDemodulators.isEmpty then c
    else Demodulation.normalForm(bank, trail, bank.order, c, activeDemodulators.toArray)

  // --- internals -----------------------------------------------------------------------------------

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

  /** Drop `c` from every shadow. The exact inverse of the shadow half of [[add]]: every line below is guarded
    * by the identical flag as its counterpart there, so the inverse relation holds by inspection rather than by
    * an argument about which collections happen to be empty. */
  private def detach(c: Clause): Unit =
    require(c.selected != null, s"ActiveSet.remove: clause ${c.id} was never activated, so its index entries " +
      "cannot be re-derived (they key on the selected literals)")
    if forwardDemodulationOn && Demodulation.isPositiveUnitEquality(bank, c) then removeDemodulatorsOf(c)
    if indexedSuperposition then updateSuperpositionEntries(c, add = false)
    if indexedResolution then updateResolutionEntries(c, add = false)
    if indexedSubsumption then { subsumptionIndex.remove(c); removeUnit(c) }
    if indexedBackwardDemod then updateDemodSubterms(c, add = false)

  /** Index (`add`) or de-index (`!add`, matched by value equality) `c`'s superposition terms: every
    * non-variable subterm of its selected literals in the into-index, and each usable maximal side of its
    * selected positive equalities in the from-index. The into-entries are re-derived by the same subterm walk
    * on both sides; the from-sides come from [[Core.Clause.fromSides]], so removal takes out exactly the
    * entries insertion put in. */
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
    var xs = c.fromSides(bank)
    while xs.nonEmpty do
      val (iFrom, fromSide, l, _) = xs.head
      val e = new FromEntry(c, iFrom, fromSide)
      if add then fromIndex.insert(l, e) else fromIndex.remove(l, e)
      xs = xs.tail

  /** Index (`add`) or de-index (`!add`) `c`'s selected non-equality literal atoms: positive atoms in the
    * positive index, negative in the negative one, so a query fetches only complementary candidates. */
  private def updateResolutionEntries(c: Clause, add: Boolean): Unit =
    val sel: Array[Int] = c.selected
    var k = 0
    while k < sel.length do
      val iLit: Int = sel(k)
      val lit: Literal = c.literals(iLit)
      if bank.headSymbol(bank.atomOf(lit)) != EqualitySymbol then
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

  /** Remove `c` from the unit sublist (no-op if absent, e.g. `c` is non-unit); swap-with-last. */
  private def removeUnit(c: Clause): Unit =
    var i = 0
    while i < units.length do
      if units(i).id == c.id then
        units(i) = units(units.length - 1)
        units.remove(units.length - 1)
        return
      i += 1

  /** Drop the demodulators whose source is the (removed) clause `c`, from the discrimination tree if
    * indexing is on (the rules recorded by [[add]], not re-derived; see [[treeRulesOf]]), else from the
    * `activeDemodulators` list. */
  private def removeDemodulatorsOf(c: Clause): Unit =
    if indexedForwardDemod then
      var xs = treeRulesOf.remove(c.id)
      if xs != null then while xs.nonEmpty do { demodTree.remove(xs.head); xs = xs.tail }
    else
      var i = 0
      while i < activeDemodulators.length do
        if activeDemodulators(i).source.id == c.id then
          activeDemodulators(i) = activeDemodulators(activeDemodulators.length - 1)
          activeDemodulators.remove(activeDemodulators.length - 1)
        else i += 1
