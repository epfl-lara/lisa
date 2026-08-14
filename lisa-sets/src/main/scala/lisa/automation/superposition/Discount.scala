package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntArrayList

import Core.*

/**
 * The DISCOUNT (given-clause) saturation loop for superposition-based clausal proving: ordered
 * resolution/factoring, the equality inferences, and simplification.
 *
 * Two clause stores, each owning its own bookkeeping: [[PassiveSet]] (unprocessed: two lazy-deletion
 * queues and the age/weight policy that picks the next given) and [[ActiveSet]] (processed: the buffer
 * plus every term and clause index that shadows it, kept in step by its own `add`/`remove`). What is left
 * here is the loop itself: each iteration selects a given clause, normal-forms and forward-simplifies it,
 * moves it into active, generates all resolvents and superpositions against the active set plus all factors
 * of itself, and inserts the (canonicalised, non-tautological) survivors back into passive. It stops at the
 * empty clause `□` (refutation) or when the passive set empties (saturation); `maxGiven` bounds the work
 * otherwise.
 *
 * Redundancy elimination, covering subsumption, unit deletion, subsumption resolution, condensation and
 * demodulation in both directions, lives in [[Simplifier]]. It runs against the active set only; passive-redundant
 * clauses are caught lazily when they are selected. None of it needs a proof obligation: a deleted clause
 * never enters `□`'s [[Justification]] DAG, and every shrunk clause is an ordinary resolvent or factor. On a
 * refutation the loop returns the empty clause, whose DAG later feeds reconstruction.
 */
object Discount:
  enum Result:
    case Refutation(empty: Clause)
    case Saturated
    case Unknown

  /** Loop instrumentation captured per `saturate`: `givenProcessed` (given clauses activated, the throughput
   *  measure), the peak sizes of the `active` and live-`passive` sets, and `passiveEnqueued` (total clauses ever
   *  put on passive). */
  final case class LoopStats(givenProcessed: Int, peakActive: Int, peakPassive: Int, passiveEnqueued: Int)

/**
 * The DISCOUNT saturation loop. Every search knob lives in [[SearchOptions]] and is imported into scope
 * below, so the loop body reads them unqualified exactly as it did when they were constructor parameters;
 * see that class for what each one means and how the defaults were chosen.
 */
final class Discount(bank: TermBank, trail: Trail, opts: SearchOptions = SearchOptions()):
  import opts.*
  import Discount.Result

  // Superposition is gated by the master `equality` flag as well as its own; when `equality` is off every
  // equality-specific inference and its upkeep is skipped throughout.
  private val superpositionOn: Boolean = equality && superposition

  // Simplification counters, owned by the [[Simplifier]] and surfaced here for tests and benchmarks.
  def forwardSubsumed: Int = simplifier.stats.forwardSubsumed
  def backwardSubsumed: Int = simplifier.stats.backwardSubsumed
  def forwardUnitDeleted: Int = simplifier.stats.forwardUnitDeleted
  def backwardUnitDeleted: Int = simplifier.stats.backwardUnitDeleted
  def forwardSubsumptionResolved: Int = simplifier.stats.forwardSubsumptionResolved
  def backwardSubsumptionResolved: Int = simplifier.stats.backwardSubsumptionResolved
  def condensed: Int = simplifier.stats.condensed

  // Throughput / scale instrumentation (reset at the start of each `saturate`).
  var givenProcessed: Int = 0                      // given clauses activated (the throughput measure)
  def peakActive: Int = active.peakSize            // max |active| over the run
  def peakPassive: Int = passive.peakSize          // max live-passive size over the run
  def passiveEnqueued: Int = passive.totalEnqueued // total clauses ever enqueued to passive

  /** Snapshot of the loop instrumentation (valid after `saturate` returns). */
  def loopStats: Discount.LoopStats = Discount.LoopStats(givenProcessed, peakActive, peakPassive, passiveEnqueued)

  // The passive (unprocessed) set and its age/weight selection policy; see [[PassiveSet]].
  private val passive: PassiveSet = new PassiveSet(opts)

  // The active (processed) set, together with every index that shadows it; see [[ActiveSet]]. All the
  // add/remove synchronisation of the demodulators and the five term/clause indices lives there, so the loop
  // below only ever says `active.add` / `active.remove`.
  private val active: ActiveSet = new ActiveSet(bank, trail, opts)

  // Every redundancy step (subsumption, unit deletion, subsumption resolution, condensation, demodulation)
  // in both directions and both the indexed and scanning variants. See [[Simplifier]].
  private val simplifier: Simplifier = new Simplifier(bank, trail, active, opts)

  // Ordering used only for the (optional) post-unification σ-maximality check on factors.
  private def kbo: KBO = bank.order.kbo

  /**
   * Saturate `initial` (plus everything derived from it). Returns [[Result.Refutation]] with the empty
   * clause if `□` is derived, [[Result.Saturated]] if the passive set empties without one, or
   * [[Result.Unknown]] if the `maxGiven` given-clause budget or the `maxMillis` wall-clock budget is
   * reached first. The time budget is checked once per given clause (cheap), so the loop stops cleanly
   * rather than relying on the caller to abandon a runaway thread.
   */
  def saturate(initial: Seq[Clause], maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue): Result =
    passive.clear(); active.reset(initial); simplifier.stats.reset()
    givenProcessed = 0
    val it = initial.iterator
    while it.hasNext do
      addPassive(it.next()) match
        case Some(empty) => return Result.Refutation(empty)
        case None => ()
    val checkTime: Boolean = maxMillis != Long.MaxValue
    val deadline: Long = if checkTime then System.nanoTime() + maxMillis * 1000000L else 0L
    while passive.nonEmpty && givenProcessed < maxGiven && (!checkTime || System.nanoTime() < deadline) do
      val popped = passive.pop()
      val demod = active.demodulate(popped) // normal-form the given against the active demodulators
      // If demodulation rewrote the given, re-canonicalise it: every other clause enters the sets via
      // addPassive → canonicalize (dropping tautologies and duplicate literals), and the selected given must
      // too -- otherwise a demodulated tautology (e.g. P(c) ∨ ¬P(c)) or duplicate literal would be activated
      // as-is and pollute active and the indices. Passive clauses are already canonical, so this is a no-op
      // (guarded by identity: `demodulate` returns the input clause unchanged when nothing rewrote).
      (if demod ne popped then Inference.canonicalize(bank, demod) else Some(popped)) match
        case None => () // demodulated to a tautology: redundant, drop it (not a processed given)
        case Some(gc) =>
          if gc.isEmpty then return Result.Refutation(gc) // demodulation closed the clause
          else
            // forward simplify the given against active: it may have been subsumed (skip) or shrunk by unit
            // deletion / subsumption resolution (process the shorter clause) by clauses that became active while
            // it sat in passive. A skip is not counted as a processed given (count activations only).
            // Called unconditionally: *which* simplifications are on is [[Simplifier]]'s business (it has its own
            // early-out). Gating here on a subset of the flags is what made `forwardSubsumptionResolution` dead
            // when it was the only one asked for.
            simplifier.forward(gc) match
              case None => () // subsumed at selection: drop it
              case Some(g) =>
                if g.isEmpty then return Result.Refutation(g) // unit deletion closed the clause
                else
                  givenProcessed += 1
                  activate(g) match
                    case Some(empty) => return Result.Refutation(empty)
                    case None => ()
    if passive.isEmpty then Result.Saturated else Result.Unknown

  /** Canonicalise `c` and add it to passive; returns the empty clause if `c` is (or simplifies to) `□`.
   *  Immediate (clause-local) simplification -- canonicalisation then condensation -- is applied first; then,
   *  when [[forwardSimplifyAtGeneration]] is on, `c` is forward-simplified against active (subsumed ⇒
   *  discarded, shrunk ⇒ the shorter clause enqueued). Forward simplification at generation is off by
   *  default -- the given is forward-simplified at selection regardless. */
  private def addPassive(c: Clause): Option[Clause] =
    Inference.canonicalize(bank, c) match
      case None => None // tautology: discard
      case Some(cc0) =>
        if cc0.isEmpty then Some(cc0)
        else
          // condensation: clause-local, run on every new clause (cannot produce □ or a tautology)
          val cc: Clause = simplifier.condense(cc0)
          val simplified: Option[Clause] =
            if forwardSimplifyAtGeneration then simplifier.forward(cc) else Some(cc)
          simplified match
            case None => None // subsumed by an active clause: discard
            case Some(cc) =>
              if cc.isEmpty then Some(cc) // unit deletion closed it
              else
                passive.enqueue(cc)
                None

  /** Move `gc` into active and generate all resolvents (against active) and factors (of itself).
   *  Backward simplification first deletes/shrinks active clauses using `gc` -- run before `gc` joins
   *  active (so it never simplifies itself) and before generation (so deleted clauses produce no
   *  inferences). A backward unit deletion that closes a clause to `□` is returned as a refutation. */
  private def activate(gc: Clause): Option[Clause] =
    val gSel: Array[Int] = gc.select(bank)
    simplifier.backwardSubsume(gc)(addPassive) match // deletes/shrinks active clauses; no-op when all its flags are off
      case Some(empty) => return Some(empty)
      case None => ()
    simplifier.backwardDemodulate(gc)(addPassive) match // if `gc` is a new unit equality, rewrite active clauses (before it joins active)
      case Some(empty) => return Some(empty)
      case None => ()
    // `gc` joins the active set (and every index that shadows it) *before* the generating inferences below, so
    // the gc-into-gc self-pair and gc's own complementary literals are found by the index queries.
    active.add(gc)
    // Precompute once per activation (invariant across the active scan): which of gc's selected literals are
    // non-equality (for ordinary resolution) and gc's usable superposition from-sides. The latter is cached on
    // the clause, so `active.add` above has already paid for it whenever the from-index is maintained.
    val gcSelNonEq: Array[Boolean] = new Array[Boolean](gSel.length)
    var gm = 0
    while gm < gSel.length do { gcSelNonEq(gm) = !isEquality(gc.literals(gSel(gm))); gm += 1 }
    val gcFromSides: List[(Int, Int, Term, Symbol)] = if superpositionOn then gc.fromSides(bank) else Nil
    // Generating inferences with gc against the active set (gc now included, so self-inferences fire). Both linear
    // arms -- resolution (always) and superposition (equality on) -- run only when indexing is off, so with
    // `fingerprintIndexing` the whole active scan is skipped in favour of the index queries below.
    if !fingerprintIndexing then
      scanGenerate(gc, gSel, gcSelNonEq, gcFromSides) match // non-indexed active scan (the A/B comparison fallback)
        case Some(empty) => return Some(empty)
        case None => ()
    else
      // Indexed generation: the same inferences via the fingerprint indices rather than the active scan.
      resolveIndexed(gc, gSel, gcSelNonEq) match
        case Some(empty) => return Some(empty)
        case None => ()
      if superpositionOn then
        superposeIndexed(gc, gSel, gcFromSides) match
          case Some(empty) => return Some(empty)
          case None => ()
    // factoring: each unordered pair of distinct selected, positive, non-equality literals, once
    // (positive factoring only; equality literals are handled by `Superposition.equalityFactoring`, run just
    // below). A literal that unifies
    // with a selected (maximal) one is itself maximal, hence also selected, so pairing within the
    // selected set loses nothing. If `factorAfterCheck`, drop a factor whose kept literal is no longer
    // (KBO-)maximal under the unifier.
    var gi2 = 0
    while gi2 < gSel.length do
      val i: Int = gSel(gi2)
      if bank.isPositive(gc.literals(i)) && !isEquality(gc.literals(i)) then
        var gj = gi2 + 1
        while gj < gSel.length do
          val j: Int = gSel(gj)
          if !isEquality(gc.literals(j)) then
            Inference.factor(bank, trail, gc, i, j) match
              case Some(f) =>
                if !factorAfterCheck || keptMaximal(f, if i < j then i else i - 1) then
                  addPassive(f) match
                    case Some(empty) => return Some(empty)
                    case None => ()
              case None => ()
          gj += 1
      gi2 += 1
    // equality resolution + equality factoring on the given (unary; enumerate all over the eligible set)
    if equality then
      val order: Order = bank.order
      addAll(Superposition.equalityResolution(bank, trail, order, gc, gSel)) match
        case Some(empty) => return Some(empty)
        case None => ()
      addAll(Superposition.equalityFactoring(bank, trail, order, gc, gSel)) match
        case Some(empty) => return Some(empty)
        case None => ()
    None

  /** Add each of `cs` to passive; returns `Some(□)` as soon as one is (or simplifies to) the empty clause. */
  private def addAll(cs: List[Clause]): Option[Clause] =
    var xs = cs
    while xs.nonEmpty do
      addPassive(xs.head) match
        case Some(empty) => return Some(empty)
        case None => ()
      xs = xs.tail
    None

  /** The non-indexed generating scan: resolution (always) and superposition (equality on) of `gc` against every
   *  active clause, the linear-scan mirror of the indexed [[resolveIndexed]]/[[superposeIndexed]] pair. Runs only
   *  when `fingerprintIndexing` is off (the A/B comparison fallback). `Some(□)` on refutation. */
  private def scanGenerate(gc: Clause, gSel: Array[Int], gcSelNonEq: Array[Boolean], gcFromSides: List[(Int, Int, Term, Symbol)]): Option[Clause] =
    var ai = 0
    while ai < active.size do
      val a: Clause = active(ai)
      val aSel: Array[Int] = a.select(bank)
      var gi = 0
      while gi < gSel.length do
        if gcSelNonEq(gi) then // equalities go to superposition / equality resolution, not here
          var aj = 0
          while aj < aSel.length do
            if !isEquality(a.literals(aSel(aj))) then
              Inference.resolve(bank, trail, gc, gSel(gi), a, aSel(aj)) match
                case Some(r) =>
                  addPassive(r) match
                    case Some(empty) => return Some(empty)
                    case None => ()
                case None => ()
            aj += 1
        gi += 1
      // superposition: gc's equations into `a` (precomputed from-sides), and `a`'s equations into gc (both
      // directions; the a == gc self-pair is done once). The caller locates + unifies; `superpose` is build-only.
      if superpositionOn then
        superposeUsing(gc, gcFromSides, a, aSel) match
          case Some(empty) => return Some(empty)
          case None => ()
        if a.id != gc.id then
          superposeUsing(a, a.fromSides(bank), gc, gSel) match
            case Some(empty) => return Some(empty)
            case None => ()
      ai += 1
    None

  /** Superpose with each of `fromC`'s precomputed `fromSides` into `intoC`'s eligible literals (`intoSel`). */
  private def superposeUsing(fromC: Clause, sides: List[(Int, Int, Term, Symbol)], intoC: Clause, intoSel: Array[Int]): Option[Clause] =
    var fs = sides
    while fs.nonEmpty do
      val (iFrom, fromSide, l, lHead) = fs.head
      var ii = 0
      while ii < intoSel.length do
        superposeAtPositions(fromC, iFrom, fromSide, l, lHead, intoC, intoSel(ii)) match
          case Some(empty) => return Some(empty)
          case None => ()
        ii += 1
      fs = fs.tail
    None

  /** Walk the non-variable subterms of `intoC`'s literal `iInto`; where the head matches the from-side `l`,
   *  save + unify + build-only `superpose` + `addPassive`. Returns `Some(□)` on refutation. */
  private def superposeAtPositions(fromC: Clause, iFrom: Int, fromSide: Int, l: Term, lHead: Symbol,
                                   intoC: Clause, iInto: Int): Option[Clause] =
    val intoAtom: Term = bank.atomOf(intoC.literals(iInto))
    var refut: Option[Clause] = None
    Superposition.foreachSubterm(bank, intoAtom) { (u, path) =>
      if bank.headSymbol(u) == lHead then // cheap head pre-check (u and l both non-variable)
        val saved: Int = trail.save()
        if trail.unify(l, 0, u, 1) then
          Superposition.superpose(bank, trail, bank.order, fromC, iFrom, fromSide, intoC, iInto, path) match
            case Some(rr) =>
              addPassive(rr) match
                case Some(empty) => refut = Some(empty)
                case None => ()
            case None => ()
        trail.restore(saved)
      refut.isDefined // stop the walk if we've derived □
    }
    refut

  // --- indexed superposition ----------------------------------------------------------------------

  /** Indexed superposition: the same inferences as [[superposeUsing]] + [[superposeFromInto]] with partners
   *  found via the fingerprint indices instead of the active scan. `gc` is already in both indices, so Pass 1
   *  (gc's equations rewriting into active into-subterms) also covers the `gc`-into-`gc` self-pair; Pass 2
   *  (active equations rewriting into gc's subterms) therefore *skips* candidates from `gc` itself. Every
   *  candidate is confirmed by a real unification in [[superposeVerified]], so the inference set is identical. */
  private def superposeIndexed(gc: Clause, gSel: Array[Int], gcFromSides: List[(Int, Int, Term, Symbol)]): Option[Clause] =
    var refut: Option[Clause] = None
    // Pass 1: gc supplies the equation; query the into-index with each usable from-side `l`.
    var fs = gcFromSides
    while fs.nonEmpty && refut.isEmpty do
      val (iFrom, fromSide, l, _) = fs.head
      active.intoCandidates(l) { e =>
        if refut.isEmpty then refut = superposeVerified(gc, iFrom, fromSide, e.clause, e.litIndex, e.pos)
      }
      fs = fs.tail
    // Pass 2: active clauses supply the equation; query the from-index with each of gc's non-variable subterms.
    var gi = 0
    while gi < gSel.length && refut.isEmpty do
      val iInto: Int = gSel(gi)
      Superposition.foreachSubterm(bank, bank.atomOf(gc.literals(iInto))) { (u, path) =>
        active.fromCandidates(u) { e =>
          if refut.isEmpty && e.clause.id != gc.id then // gc-into-gc already done in Pass 1
            refut = superposeVerified(e.clause, e.litIndex, e.side, gc, iInto, path.toIntArray)
        }
        refut.isDefined // stop the subterm walk on refutation
      }
      gi += 1
    refut

  /** Verify + build one located superposition: unify `fromC`'s side `fromSide` with `intoC`'s subterm at `pos`,
   *  then the build-only [[Superposition.superpose]] and `addPassive`. Restores the trail. `Some(□)` on refutation. */
  private def superposeVerified(fromC: Clause, iFrom: Int, fromSide: Int, intoC: Clause, iInto: Int, pos: Array[Int]): Option[Clause] =
    val l: Term = bank.arg(bank.atomOf(fromC.literals(iFrom)), fromSide)
    val u: Term = Superposition.subtermAt(bank, bank.atomOf(intoC.literals(iInto)), pos)
    val saved: Int = trail.save()
    var res: Option[Clause] = None
    if trail.unify(l, 0, u, 1) then
      Superposition.superpose(bank, trail, bank.order, fromC, iFrom, fromSide, intoC, iInto, IntArrayList.wrap(pos)) match
        case Some(rr) => res = addPassive(rr)
        case None => ()
    trail.restore(saved)
    res

  // --- indexed resolution -------------------------------------------------------------------------

  /** Indexed ordinary resolution: for each of gc's selected non-equality literals, query the *opposite*-polarity
   *  literal index with its atom and confirm each candidate with [[Inference.resolve]] (which re-checks
   *  complementarity and does the real unification). gc is already indexed, so its own complementary literals are
   *  returned -- the self-resolutions the linear scan also performs. A single pass over gc's literals produces
   *  each ordered partner pair exactly once (as the scan does), so no self-skip is needed. `Some(□)` on refutation. */
  private def resolveIndexed(gc: Clause, gSel: Array[Int], gcSelNonEq: Array[Boolean]): Option[Clause] =
    var refut: Option[Clause] = None
    var gi = 0
    while gi < gSel.length && refut.isEmpty do
      if gcSelNonEq(gi) then
        val iLit: Int = gSel(gi)
        val lit: Literal = gc.literals(iLit)
        active.resolutionPartners(bank.isPositive(lit), bank.atomOf(lit)) { e =>
          if refut.isEmpty then
            Inference.resolve(bank, trail, gc, iLit, e.clause, e.litIndex) match
              case Some(r) => refut = addPassive(r)
              case None => ()
        }
      gi += 1
    refut

  /** Whether `lit`'s atom is an equality `s = t` (ordinary resolution/factoring skip these). */
  private def isEquality(lit: Literal): Boolean =
    bank.headSymbol(bank.atomOf(lit)) == EqualitySymbol

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
