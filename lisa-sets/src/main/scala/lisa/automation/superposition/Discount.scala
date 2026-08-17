package lisa.automation.superposition

import Core.*

/** What a saturation returns: its verdict, and the instrumentation gathered while reaching it. */
object Discount:

  /** The three outcomes of a saturation: `□` was derived, the passive set emptied without it (so the set is
   *  satisfiable, a decision), or a budget ran out (so nothing is decided). [[Bridge.Outcome]] mirrors these. */
  enum Result:
    case Refutation(empty: Clause)
    case Saturated
    case Unknown

  /** Loop instrumentation per `saturate`: clauses activated (the throughput measure), the peak `active` and
   *  live-`passive` sizes, and the total ever enqueued to passive. */
  final case class LoopStats(givenProcessed: Int, peakActive: Int, peakPassive: Int, passiveEnqueued: Int)

/** The DISCOUNT given-clause saturation loop. Each iteration takes a clause from [[PassiveSet]], normal-forms
  * and forward-simplifies it, moves it into [[ActiveSet]], generates every inference against the active clauses
  * and every factor of itself, and returns the survivors to passive. It stops at the empty clause, at an empty
  * passive set, or at a budget.
  *
  * The two halves of the work are elsewhere: [[Generator]] performs the inferences, [[Simplifier]] the
  * deletions and the shrinking, leaving the iteration, the two clause sets, and the one decision about where a
  * new clause goes. Simplification runs against the active set only; a redundant passive clause is caught when
  * it is selected. Every search knob lives in [[SearchOptions]], imported below so the loop reads them
  * unqualified. */
final class Discount(bank: TermBank, trail: Trail, initial: Seq[Clause], opts: SearchOptions = SearchOptions()):
  import opts.*
  import Discount.Result

  /** How much each simplification fired, for tests and benchmarks. Owned by the [[Simplifier]] and handed on
    * whole: seven one-line accessors used to forward the seven counters individually, which meant an eighth
    * counter needed an eighth accessor here before anything could read it. */
  def stats: SimplificationStats = simplifier.stats

  // Throughput / scale instrumentation.
  private var givenProcessed: Int = 0              // given clauses activated (the throughput measure)
  def peakActive: Int = active.peakSize            // max |active| over the run
  def peakPassive: Int = passive.peakSize          // max live-passive size over the run
  def passiveEnqueued: Int = passive.totalEnqueued // total clauses ever enqueued to passive

  /** Snapshot of the loop instrumentation (valid after `saturate` returns). */
  def loopStats: Discount.LoopStats = Discount.LoopStats(givenProcessed, peakActive, peakPassive, passiveEnqueued)

  // The passive (unprocessed) set and its age/weight selection policy; see [[PassiveSet]].
  private val passive: PassiveSet = new PassiveSet(opts)

  // The active (processed) set, together with every index that shadows it; see [[ActiveSet]]. All the
  // add/remove synchronisation of the demodulators and the indices lives there, so the loop below only ever
  // says `active.add` / `active.remove`.
  private val active: ActiveSet = new ActiveSet(bank, trail, initial, opts)

  // Every redundancy step (subsumption, unit deletion, subsumption resolution, condensation, demodulation), in
  // both directions. See [[Simplifier]].
  private val simplifier: Simplifier = new Simplifier(bank, trail, active, opts)

  // Every generating inference (resolution, superposition, factoring, the two unary equality rules). See
  // [[Generator]]. Its conclusions arrive through `addPassive`, which is where the loop takes over again.
  private val generator: Generator = new Generator(bank, trail, active, opts)(addPassive)

  /** The empty clause, once some step derives it; `null` until then.
    *
    * Deriving `□` ends the run, so every step that can produce a clause has to be able to abandon the work
    * above it. That used to be spelled by returning `Option[Clause]` and matching on it at each of the
    * twenty-odd call sites, three lines apiece, which buried the loop's actual control flow. The refutation is
    * a once-per-run event, so it does not belong in the return type of a per-clause function: it is recorded
    * here and every such function returns `true` for "stop, `□` was derived". */
  private var refutation: Clause = null

  /** Saturate the clause set this loop was built on, plus everything derived from it. Returns
    * [[Result.Refutation]] with the empty clause if `□` is derived, [[Result.Saturated]] if the passive set
    * empties without one, or [[Result.Unknown]] if the `maxGiven` given-clause budget or the `maxMillis`
    * wall-clock budget is reached first. The time budget is checked once per given clause (cheap), so the loop
    * stops cleanly rather than relying on the caller to abandon a runaway thread.
    *
    * '''Call once.''' A `Discount` runs one saturation: its two clause sets, its indices and its counters are
    * built for that problem and never cleared. To saturate again, build another -- which is all the clearing
    * used to do, at the cost of every one of those structures carrying a reset path nothing called. */
  def saturate(maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue): Result =
    val it = initial.iterator
    while it.hasNext do
      if addPassive(it.next()) then return Result.Refutation(refutation)
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
            // forward simplify the given against active: clauses that became active while it sat in passive may
            // subsume it (skip) or shrink it (process the shorter clause). A skip is not a processed given.
            // Called unconditionally: *which* simplifications are on is [[Simplifier]]'s business.
            simplifier.forward(gc) match
              case None => () // subsumed at selection: drop it
              case Some(g) =>
                if g.isEmpty then return Result.Refutation(g) // unit deletion closed the clause
                else
                  givenProcessed += 1
                  if activate(g) then return Result.Refutation(refutation)
    if passive.isEmpty then Result.Saturated else Result.Unknown

  /** Record `empty` as the run's refutation and report `true`, so that every producer of clauses reads
   *  `if addPassive(c) then return true`. */
  private def found(empty: Clause): Boolean = { refutation = empty; true }

  /** Canonicalise `c` and add it to passive; `true` if `c` is (or simplifies to) `□`, which is then in
   *  [[refutation]]. Immediate (clause-local) simplification -- canonicalisation then condensation -- is
   *  applied first; then, when [[forwardSimplifyAtGeneration]] is on, `c` is forward-simplified against active
   *  (subsumed ⇒ discarded, shrunk ⇒ the shorter clause enqueued). Forward simplification at generation is off
   *  by default -- the given is forward-simplified at selection regardless. */
  private def addPassive(c: Clause): Boolean =
    Inference.canonicalize(bank, c) match
      case None => false // tautology: discard
      case Some(cc0) =>
        if cc0.isEmpty then found(cc0)
        else
          // condensation: clause-local, run on every new clause (cannot produce □ or a tautology)
          val cc: Clause = simplifier.condense(cc0)
          val simplified: Option[Clause] =
            if forwardSimplifyAtGeneration then simplifier.forward(cc) else Some(cc)
          simplified match
            case None => false // subsumed by an active clause: discard
            case Some(s) =>
              if s.isEmpty then found(s) // unit deletion closed it
              else
                passive.enqueue(s)
                false

  /** Move `gc` into the active set and generate everything it yields there.
    *
    * Backward simplification runs first: before `gc` joins active, so that it never simplifies itself, and
    * before generation, so that deleted clauses produce no inferences. Then `gc` joins the active set and every
    * index that shadows it, *before* the generating inferences, so that the gc-into-gc self-pair and gc's own
    * complementary literals come back from the index queries. `true` if anything along the way closes a clause
    * to `□`. */
  private def activate(gc: Clause): Boolean =
    // The selection, computed here because `active.add` keys its indices on it and reads it rather than
    // computing it, so it has to exist by then.
    val gSel: Array[Int] = gc.select(bank)
    if simplifier.backwardSubsume(gc)(addPassive) then return true //    deletes/shrinks active clauses
    if simplifier.backwardDemodulate(gc)(addPassive) then return true // rewrites them if `gc` is a unit equality
    active.add(gc)
    generator.generate(gc, gSel)
