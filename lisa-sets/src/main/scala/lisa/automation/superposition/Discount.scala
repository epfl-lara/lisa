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
  * deletions and the shrinkings. Every search knob lives in [[SearchOptions]], imported below so the loop reads them
  * unqualified. */
final class Discount(bank: TermBank, trail: Trail, initial: Seq[Clause], opts: SearchOptions = SearchOptions()):
  import opts.*
  import Discount.Result

  /** How much each simplification fired, for tests and benchmarks. Owned by the [[Simplifier]]. */
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
  // add/remove synchronisation of the demodulators and the indices lives there.
  private val active: ActiveSet = new ActiveSet(bank, trail, initial, opts)

  // Every redundancy step (subsumption, unit deletion, subsumption resolution, condensation, demodulation), in
  // both directions. See [[Simplifier]].
  private val simplifier: Simplifier = new Simplifier(bank, trail, active, opts)

  // Every generating inference (resolution, superposition, factoring, the two unary equality rules). See
  // [[Generator]]. Its conclusions arrive through `addPassive`, which is where the loop takes over again.
  private val generator: Generator = new Generator(bank, trail, active, opts)(addPassive)

  /** The empty clause, once some step derives it; `null` until then. */
  private var refutation: Clause = null

  /** Saturate the clause set this loop was built on. Returns
    * [[Result.Refutation]] with the empty clause if `□` is derived, [[Result.Saturated]] if the passive set
    * empties without one, or [[Result.Unknown]] if the `maxGiven` given-clause budget or the `maxMillis`
    * wall-clock budget is reached first. The time budget is checked once per given clause (cheap). */
  def saturate(maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue): Result =
    val it = initial.iterator
    while it.hasNext do
      if addPassive(it.next()) then return Result.Refutation(refutation)
    val checkTime: Boolean = maxMillis != Long.MaxValue
    val deadline: Long = if checkTime then System.nanoTime() + maxMillis * 1000000L else 0L
    while passive.nonEmpty && givenProcessed < maxGiven && (!checkTime || System.nanoTime() < deadline) do
      val popped = passive.pop()
      val demod = active.demodulate(popped) // normal-form the given against the active demodulators
      // If demodulation rewrote the given, re-canonicalise it.
      (if demod ne popped then Inference.canonicalize(bank, demod) else Some(popped)) match
        case None => () // demodulated to a tautology: redundant, drop it (not a processed given)
        case Some(gc) =>
          if gc.isEmpty then return Result.Refutation(gc) // demodulation closed the clause
          else
            // forward simplify the given against active: clauses that became active while it sat in passive may
            // subsume it (skip) or shrink it (process the shorter clause).
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
   *  [[refutation]]. Simplification of the close from itself only -- canonicalisation then condensation -- is
   *  applied first; then, when [[forwardSimplifyAtGeneration]] is on, `c` is forward-simplified against active
   *  (subsumed ⇒ discarded, shrunk ⇒ the shorter clause enqueued). */
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

  /** Move `gc` into the active set and generate everything it yields there. `true` if anything along the way closes a clause
    * to `□`. */
  private def activate(gc: Clause): Boolean =
    // The selection, computed here because `active.add` keys its indices on it and reads it rather than
    // computing it, so it has to exist by then.
    val gSel: Array[Int] = gc.select(bank)
    if simplifier.backwardSubsume(gc)(addPassive) then return true //    deletes/shrinks active clauses
    if simplifier.backwardDemodulate(gc)(addPassive) then return true // rewrites them if `gc` is a unit equality
    active.add(gc)
    generator.generate(gc, gSel)
